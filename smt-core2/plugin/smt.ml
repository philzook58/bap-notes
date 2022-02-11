open Core_kernel
open Bap_core_theory
open Bap_main
open Bap.Std
open KB.Syntax

let package = "smt"
let herbrand_provides = [
  "syntax";
  "herbrand";
  "lisp";
  "debug";
  "core:eff";
  "core:val"
]

let domain = KB.Domain.optional "cst"
    ~equal:Sexp.equal
    ~inspect:ident


let wp_domain : (Sexp.t -> Var.t list -> Sexp.t) option KB.Domain.t = KB.Domain.optional
    ~inspect:(fun wp -> wp (Sexp.Atom "POST") [Var.create "ALLVARS" (Imm 32)]) 
    (* I guess we could have equality based on instatiating the transformer? *)
    ~equal:(fun _wp _wp' -> true) "wp"

let eslot = KB.Class.property Theory.Semantics.cls "eff"
    ~package
    ~public:true
    wp_domain

let pslot = KB.Class.property Theory.Value.cls "val"
    ~package
    ~public:true
    domain

    (*
    Current thinking is chc isn't really a program property because it is dependent upon variables in scope
let chc = KB.Class.property Theory.Program.cls "chc-val"
    ~package
    ~public:true
    domain
    *)

let addr_size = 32

module Z3Helpers = struct
  let atom s = Sexp.Atom s

  (* Use of list is questionable in general case. *)
  let list = function
    | Sexp.Atom "let" :: rest -> Sexp.List (Sexp.Atom "let" :: rest)
    | [Sexp.Atom op;
       List ((Atom opx) :: xs);
       List ((Atom opy) :: ys)]
      when String.(op = opx && op = opy) ->
      Sexp.List (Atom op :: List.append xs ys)
    | [Sexp.Atom op; List ((Atom opx) :: xs); y]
      when String.(op = opx) ->
      Sexp.List (Sexp.Atom op :: xs@[y])
    | [Sexp.Atom op; x; List ((Atom opy) :: ys)]
      when String.(op = opy) ->
      Sexp.List (Sexp.Atom op :: x :: ys)
    | xs -> Sexp.List xs

  let app x xs = list (atom x :: xs)

  let escapes = [
    "%", "%%";
    "#", "%P";
  ]
  let escape s = List.fold escapes ~init:s 
    ~f:(fun s (pattern,with_) -> String.substr_replace_all s ~pattern ~with_)

  let unescape s = List.fold (List.rev escapes) ~init:s 
    ~f:(fun s (with_,pattern) -> String.substr_replace_all s ~pattern ~with_)

  let utag a b = list [atom "_"; a; b]

  let z3_const s x =
    let size = Theory.Bitv.size s in
    let x = Bitvec.to_bigint x in
    if Int.rem size 4 = 0 then
      let size = size / 4 in (* print in hex *)
      let str = Z.format (sprintf "%%0%dx" size) x in
      sprintf "#x%s" str
    else
      let str = Z.format (sprintf "%%0%db" size) x in
      sprintf "#b%s" str


  let z3_sort (s : 'a Theory.Value.Sort.t) : Sexp.t = 
    let s = Theory.Value.Sort.forget s in
    match Theory.Bitv.refine s with
    | Some s -> utag (atom "BitVec") (atom @@ Int.to_string (Theory.Bitv.size s))
    | None -> 
      match Theory.Bool.refine s with
      | Some _ -> atom "Bool"
      | None -> atom "failure to refine z3 sort"

  let svar v = atom @@ escape @@ (Theory.Var.name v)
  let sexp_of_var' v = atom @@ escape @@ (Var.to_string v)
  let z3_sort' (typ : typ) = 
    let bitvec n = utag (atom "BitVec") (atom @@ Int.to_string n) in
    match typ with
    | Imm n ->  bitvec n
    | Mem (addr_size, size) -> 
      let range_size = Size.in_bits size in
      let dom_size = Size.in_bits addr_size in
      app "Array" [bitvec dom_size; bitvec range_size]
    | _ -> failwith (sprintf "unimplemented z3_sort %a" Type.pps typ)
  let vars_with_sorts (vars : Var.t list) : (Sexp.t * Sexp.t) list =
    List.map vars ~f:(fun v ->
        (sexp_of_var' v, z3_sort' (Var.typ v)))
  let var_sorts' vars : Sexp.t list =
    List.map vars ~f:(fun v ->
        list [sexp_of_var' v; z3_sort' (Var.typ v)])
  let var_sorts vars : Sexp.t =
    list @@ var_sorts' vars
end

module WP_SMT : Theory.Core = struct

  include Theory.Empty
  open Z3Helpers

  let pure s cst = KB.Value.put pslot (Theory.Value.empty s) (Some cst)
  let eff s cst = KB.Value.put eslot (Theory.Effect.empty s) (Some cst)
  let data = eff Theory.Effect.Sort.bot
  let ctrl = eff Theory.Effect.Sort.bot
  let ret = KB.return

  let psort = Theory.Value.sort
  let esort = Theory.Effect.sort

  (** [(>>->)] is like KB.bind that also supplies a sort and pulls pslot out of the value *)
  let (>>->) x f =
    x >>= fun v ->
    let s = psort v in
    f s (KB.Value.get pslot v)

  (** [(>>|>)] is like KB.map that also supplies a sort and pulls pslot out of the value *)
  let (>>|>) x f = x >>-> fun s v -> ret (f s v)

  (** [(>>->?)] is like KB.bind that also supplies a sort and pulls pslot out of the value. If the slot is None
      it returns an empty Value, which does nothing
  *)
  let (>>->?) x f =
    x >>= fun v ->
    let s = psort v in
    match KB.Value.get pslot v with
    | None -> ret (Theory.Value.empty s)
    | Some v -> f s v

  let (>>|>?) x f = x >>->? fun s v -> ret (f s v)

  (** like >>-> but for effect slot instead of values *)
  let (>>=>) x f =
    x >>= fun v ->
    let s = esort v in
    f s (KB.Value.get eslot v)
  (** Rather than returning empty effect, this returns the WP transformer for SKIP. Questionable *)
  let (>>=>?) x f =
    x >>= fun v ->
    let s = esort v in
    match KB.Value.get eslot v with
    | None -> f s (fun post vars -> post)
    | Some x -> f s x


  let empty = Theory.Value.empty

  let unary_s s op x = x >>|> fun _ -> function
    | None -> empty s
    | Some v -> pure s @@ app op [v]

  let unary op x = x >>|>? fun s v -> pure s @@ app op [v]

  (** Why a monoid? Because the implicit use of the list combinator above. *)
  let monoid_s s op x y =
    x >>-> fun _ x ->
    y >>|> fun _ y ->
    match x, y with
    | Some x, Some y -> pure s @@ app op [x; y]
    | _ -> empty s

  let monoid op x y =
    x >>->? fun s x ->
    y >>|>? fun _ y ->
    pure s @@ app op [x; y]


  module Minimal : Theory.Minimal = struct
    (** We have made Bool represented by 1 bit bitvectors.
        The type system makes me think this shouldn't have to be the case *)
    let b0 = ret@@pure Theory.Bool.t (atom "#b0")
    let b1 = ret@@pure Theory.Bool.t (atom "#b1")

    let unk s = ret@@empty s

    let var v =
      let s = Theory.Var.sort v in
      ret @@ pure s @@ svar v

    let let_ v x y =
      x >>-> fun _ x ->
      y >>|> fun s y ->
      let name = Theory.Var.name v in
      match x,y with
      | Some x, Some y ->
        pure s@@app "let" [list [atom name; x]; y]
      | _ -> empty s

    let ite c x y =
      c >>-> fun _ c ->
      x >>->? fun s x ->
      y >>|>? fun _ y -> match c with
      | None -> empty s
      | Some c -> pure s@@app "ite" [app "=" [c; atom "#b1"]; x; y]

    let inv = unary "bvnot"
    let and_ = monoid "bvand"
    let or_ = monoid "bvor"

    let int s x = ret@@pure s@@atom (z3_const s x)
    let msb x = 
      let s = Theory.Bool.t in
      x >>|> fun s' -> function
      | None -> empty s
      | Some v -> 
        let size = atom @@ string_of_int @@ Theory.Bitv.size s' in
        pure s @@ 
        app "ite" [
          app "=" [app "extract" [size; size; v]; atom "#b1"]; (* size - 1? We'll get an error if this is wrong. Fine. *)
          atom "true"; 
          atom "false"]

    let lsb x = 
      let s = Theory.Bool.t in
      x >>|> fun _ -> function
      | None -> empty s
      | Some v -> pure s @@ list [list [atom "_"; atom "extract"; atom "0"; atom "0"]; v]
    (*app "ite" [
           app "=" [list [list [atom "_"; atom "extract"; atom "0"; atom "0"]; v]; atom "#b1"];
           atom "true"; 
           atom "false"] *)
    let neg x = unary "bvneg" x
    let not x = unary "bvnot" x
    let add x = monoid "bvadd" x
    let sub x = monoid "bvsub" x
    let mul x = monoid "bvmul" x
    let div x = monoid "bvdiv" x
    let sdiv x = monoid "bvsdiv" x
    let modulo x = monoid "mod?" x
    let smodulo x = monoid "bvsmod" x
    let logand x = monoid "bvand" x
    let logor x = monoid "bvor" x
    let logxor x = monoid "bvxor" x

    let genshift name fill x off =
      fill >>-> fun _ fill ->
      x >>-> fun s x ->
      off >>|> fun _ off ->
      match fill, x, off with
      | Some fill, Some x, Some off ->
        pure s @@ app name [fill; x; off]
      | _ -> empty s
    let shiftr fill x off =
      fill >>-> fun _ fill ->
      x >>-> fun s x ->
      off >>|> fun _ off ->
      match fill, x, off with
      | Some fill, Some x, Some off ->
        pure s @@  app "ite" [app "=" [fill; atom "#b1"];
                              app "bvlshr" [x ; off]
                             ; app "bvlshr" [x ; off] (* do something else here *)
                             ]
      | _ -> empty s
    let shiftl fill x off =
      fill >>-> fun _ fill ->
      x >>-> fun s x ->
      off >>|> fun _ off ->
      match fill, x, off with
      | Some fill, Some x, Some off ->
        pure s @@  app "ite" [app "=" [fill; atom "#b1"];
                              app "bvshl" [x ; off]
                             ; app "bvshl" [x ; off] (* do something else here *)
                             ]
      | _ -> empty s
    let sle x y = (* monoid_s Theory.Bool.t "bvsle" x *)
      x >>-> fun _ x ->
      y >>|> fun _ y ->
      match x, y with
      | Some x, Some y -> pure Theory.Bool.t @@ app "ite" [app "bvsle" [x; y]; atom "#b1"; atom "#b0"] 
      | _ -> empty Theory.Bool.t


    let ule x y = 
      x >>-> fun _ x ->
      y >>|> fun _ y ->
      match x, y with
      | Some x, Some y -> pure Theory.Bool.t @@ app "ite" [app "bvule" [x; y]; atom "#b1"; atom "#b0"] 
      | _ -> empty Theory.Bool.t
    (* monoid_s Theory.Bool.t "bvule" x *)


    let cast s fill exp =
      fill >>-> fun _ fill ->
      exp >>|> fun s' x ->
      let newsize = Theory.Bitv.size s' in
      let size = Theory.Bitv.size s in
      (** let ct = sprintf "%d" @@  in *)
      match fill, x  with
      | Some fill, Some x ->
        (* TODO: deal with fill *)
        if Theory.Value.Sort.same s s'
        then pure s x
        else if size < newsize then
          let pad = z3_const (Theory.Bitv.define Int.(newsize - size)) Bitvec.zero in
          pure s @@ app "concat" [atom pad ; x]
        else
          pure s @@ app "extract" [atom "1" ; atom (string_of_int newsize); x]
      (* pure s@@list [
         atom "cast";
         atom ct;
         fill;
         x
         ] *)
      | _ -> empty s

    let concat s xs =
      List.map xs ~f:(fun x -> x >>|> fun _ -> ident) |>
      KB.List.all >>| Option.all >>| function
      | None -> empty s
      | Some xs -> pure s @@ app "concat" xs

    let append s x y = monoid_s s "concat" x y (* Do I need to cast the result too? *)

    let load m x =
      m >>-> fun s m ->
      x >>|> fun _ x ->
      let s = Theory.Mem.vals s in
      match m, x with
      | Some m, Some x -> pure s @@ app "select" [m; x]
      | _ -> empty s

    let store m p x =
      m >>-> fun s m ->
      p >>-> fun _ p ->
      x >>|> fun _ x ->
      match m, p, x with
      | Some m, Some p, Some x ->
        pure s @@ app "store" [m; p; x]
      | _ -> empty s

    let nil = Theory.Effect.empty Theory.Effect.Sort.bot

    let perform eff = ret (Theory.Effect.empty eff)

    let set v x = x >>|> fun _ x ->
      match x with
      | None -> nil
      | Some x -> data@@
        fun post _ -> 
        list [atom "let"; 
              list [list [svar v; x]];
              post]

    let jmp x = x >>|> fun _ x -> match x with
      | None -> nil
      | Some x -> ctrl@@ fun post all_vars -> 
        let all_vars = List.map ~f:sexp_of_var' all_vars in
       (*  list [atom "and";  *)
              list (atom "reach-state" :: x :: all_vars)
             (*  ; post] *)

    let goto dst =
      KB.collect Theory.Label.addr dst >>= function
      | Some dst ->
        ret@@ctrl@@ fun post vars -> app "reach-state" (atom (z3_const (Theory.Bitv.define addr_size) dst) :: List.map ~f:sexp_of_var' vars)
      | None ->
        KB.Object.repr Theory.Program.cls dst >>= fun dst ->
        ret@@ctrl@@ fun post vars -> app "goto TODO" [atom dst]

    let both s xs ys =
      match xs,ys with
      | None,None -> ret nil
      | Some r, None
      | None, Some r -> ret@@eff s r
      | Some xs, Some ys ->
        ret@@eff s@@
        fun post vars -> (xs (ys post vars) vars)

    let seq xs ys =
      xs >>=> fun s xs ->
      ys >>=> fun _ ys ->
      both s xs ys

    let blk label xs ys =
      xs >>=> fun _ xs ->
      ys >>=> fun _ ys ->
      (* Questions here:
         Should I be producing also a forall term?
         Should I be checking that label is null?
      *)
      (* fun s vars -> list [
         atom "and";
         (wpdata (wpctrl s));
         [forall  ;atom "=>" ; atom ""]
         ] "(forall %a (=> (label %a %a) %a) )" pp_varset varset pp_label label pp_varset vars
      *)
      both Theory.Effect.Sort.top xs ys (* >>=>? fun s wp ->
                                           ret@@eff s@@ fun post vars -> 
                                           let all_vars = List.map ~f:sexp_of_var' vars in
                                           let bind_vars = List.map vars ~f:(fun v ->
                                           list [sexp_of_var' v ; z3_sort' (Var.typ v) ]
                                           ) in
                                           let wp = wp post vars in
                                           wp *)
    (* list [
       atom "and";
       wp;
       list [atom "forall"; 
        list bind_vars; (* put types in there.*)
        list [atom "=>";
             list (atom "label" :: (atom @@ Tid.to_string label) :: all_vars);
             wp
        ]
       ]
       ] *)
        (*

        *)
    let repeat cnd body =
      cnd >>-> fun _ cnd ->
      body >>=>? fun s body ->
      match cnd with
      | None -> ret@@nil
      | Some cnd ->
        ret@@eff s@@ fun _ _ -> failwith "repeat not implemented"

    let branch cnd yes nay =
      cnd >>-> fun _ cnd ->
      yes >>=>? fun s yes ->
      nay >>=>? fun _ nay ->
      match cnd with
      | None -> ret@@nil
      | Some cnd ->
        let cnd = app "=" [cnd; atom "#b1"] in
        ret@@eff s@@ fun post vars -> app "ite" [cnd; yes post vars; nay post vars]
  end
  include Theory.Basic.Make(Minimal)
    (* SEE TODO FILE *)
end

(*
let promise_chc () = 
  let open Z3Helpers in
  KB.promise chc (fun label ->
    KB.collect Theory.Label.addr label >>= fun addr ->
    KB.collect Theory.Semantics.slot label >>= fun sem ->
      let (let* ) x f = Option.bind x ~f in
      KB.return (
      let* wp = KB.Value.get eslot sem in 
      let* addr = addr in
      let addr = z3_const (Theory.Bitv.define addr_size) addr in
      let all_vars =[atom "ALLVARS"] in
      let bind_vars = list all_vars in
      let fallthrough = app "label" (atom "FALLTHROUGH" :: all_vars) in
      Option.return @@ 
      app "forall"
      [ bind_vars;
        app "=>"
           [app "label" (atom addr :: all_vars ) ;
           wp fallthrough []]]
     (* KB.return @@ Option.map (KB.Value.get eslot sem) ~f:(fun wp -> wp (Sexp.Atom "true") []) *)
    ))

    (*
                  list [atom "forall"; 
                    list bind_vars; (* put types in there.*)
                    list [atom "=>";
                         list (atom "label" :: (atom @@ Tid.to_string label) :: all_vars);
                         wp
                    ]
              ]
            ] *)
            *)

let herbrand_enabled = Extension.Configuration.parameter
    Extension.Type.(bool =? false) "enable"
    ~as_flag:true
(* ~aliases:["herbrand"; "debug"] *)

let enable_herbrand () =
  Theory.declare
    ~provides:herbrand_provides
    ~desc:"provides smt interpretation"
    ~package
    ~name:"syntax" (KB.return (module WP_SMT : Theory.Core))

let pp_rule ppf proj =
  let open Z3Helpers in
  let kb = Toplevel.current () in
  let res = KB.run Theory.Program.cls 
      (KB.objects Theory.Program.cls >>= fun progs ->
        let* allvars = KB.Seq.fold progs ~init:Var.Set.empty 
            ~f:(fun vars prog -> 
                KB.collect Theory.Semantics.slot prog >>= fun sem ->
                let vars' = KB.Value.get Allvars.eslot sem in
                KB.return @@ Var.Set.union vars vars'
              ) 
        in
        let allvars = Var.Set.to_list allvars in
        (* Format.fprintf ppf "#define ALLVARS"; *)
        let sorts = list @@ utag (atom "BitVec") (atom (string_of_int addr_size)) :: List.map ~f:(fun v -> z3_sort' (Var.typ v)) allvars in
        Format.fprintf ppf "(declare-rel reach-state %a)@ " Sexp.pp_hum sorts;
        List.iter (var_sorts' allvars) ~f:(fun sexp ->
            let List sexp = sexp in
            let sexp = app "declare-var" sexp in
            Format.fprintf ppf "%a@ " Sexp.pp_hum sexp;
          );


        KB.Seq.iter progs ~f:(fun prog -> 
            KB.collect Theory.Semantics.slot prog >>= fun sem ->
            let wp = KB.Value.get eslot sem in 
            match wp with
            | None -> KB.return ()
            | Some wp -> 
              KB.collect Theory.Label.addr prog >>= fun addr ->
              match addr with
              | None -> KB.return ()
              | Some addr ->
                let z3_addr = z3_const (Theory.Bitv.define addr_size) addr in
                let all_vars = List.map ~f:Z3Helpers.sexp_of_var' allvars in
                (* KB.collect chc prog >>= fun chc -> *)
                KB.collect Memory.slot prog >>= fun mem ->
                match mem with
                | None -> KB.return ()
                | Some mem ->
                  let fall_addr = Bitvec.(addr + Bitvec.of_string (string_of_int (Memory.length mem))) in
                  let fall_addr =if addr_size = 64 then 
                      z3_const (Theory.Bitv.define addr_size) Bitvec.(fall_addr mod m64)
                    else  begin
                      assert (addr_size = 32);
                      z3_const (Theory.Bitv.define addr_size) Bitvec.(fall_addr mod m32)
                    end
                  in
                  let fallthrough = app "reach-state" (atom fall_addr :: all_vars) in
                  let chc =  app "rule" [app "=>"
                                                [app "reach-state" (atom z3_addr :: all_vars ) ;
                                                  wp fallthrough allvars]]
                  in
                  Format.fprintf ppf ";%a@\n" Bitvec.pp addr;
                  Format.fprintf ppf "%a@ " Sexp.pp_hum chc;
                  KB.return ()
          ) >>= fun () ->
        KB.Object.create Theory.Program.cls
      ) 
      kb
  in
  match res with
  | Ok _ -> ()
  | Error _ -> failwith "KB error"

let pp_chc ppf proj =
  let open Z3Helpers in
  let kb = Toplevel.current () in
  let res = KB.run Theory.Program.cls 
      (KB.objects Theory.Program.cls >>= fun progs ->
       let* allvars = KB.Seq.fold progs ~init:Var.Set.empty 
           ~f:(fun vars prog -> 
               KB.collect Theory.Semantics.slot prog >>= fun sem ->
               let vars' = KB.Value.get Allvars.eslot sem in
               KB.return @@ Var.Set.union vars vars'
             ) 
       in
       let allvars = Var.Set.to_list allvars in
       (* Format.fprintf ppf "#define ALLVARS"; *)
       let sorts = list @@ utag (atom "BitVec") (atom (string_of_int addr_size)) :: List.map ~f:(fun v -> z3_sort' (Var.typ v)) allvars in
       Format.fprintf ppf "(declare-fun reach-state %a Bool)@ " Sexp.pp_hum sorts;
       List.iter (var_sorts' allvars) ~f:(fun sexp ->
           let List sexp = sexp in
           let sexp = app "declare-const" sexp in
           Format.fprintf ppf "%a@ " Sexp.pp_hum sexp;
         );


       KB.Seq.iter progs ~f:(fun prog -> 
           KB.collect Theory.Semantics.slot prog >>= fun sem ->
           let wp = KB.Value.get eslot sem in 
           match wp with
           | None -> KB.return ()
           | Some wp -> 
             KB.collect Theory.Label.addr prog >>= fun addr ->
             match addr with
             | None -> KB.return ()
             | Some addr ->
               let z3_addr = z3_const (Theory.Bitv.define addr_size) addr in
               let all_vars = List.map ~f:Z3Helpers.sexp_of_var' allvars in
               (* KB.collect chc prog >>= fun chc -> *)
               KB.collect Memory.slot prog >>= fun mem ->
               match mem with
               | None -> KB.return ()
               | Some mem ->
                 let fall_addr = Bitvec.(addr + Bitvec.of_string (string_of_int (Memory.length mem))) in
                 let fall_addr =if addr_size = 64 then 
                     z3_const (Theory.Bitv.define addr_size) Bitvec.(fall_addr mod m64)
                   else  begin
                     assert (addr_size = 32);
                     z3_const (Theory.Bitv.define addr_size) Bitvec.(fall_addr mod m32)
                   end
                 in
                 let fallthrough = app "reach-state" (atom fall_addr :: all_vars) in
                 let bind_vars = var_sorts allvars in
                 let chc =  app "assert" [app "forall"
                                            [ bind_vars;
                                              app "=>"
                                                [app "reach-state" (atom z3_addr :: all_vars ) ;
                                                 wp fallthrough allvars]]]
                 in
                 Format.fprintf ppf ";%a@\n" Bitvec.pp addr;
                 let bil = KB.Value.get Bil.slot sem in 
                 let bil = String.substr_replace_all (Bil.to_string bil) ~pattern:"\n" ~with_:"\n;" in
                 Format.fprintf ppf ";%s@\n" bil;
                 Format.fprintf ppf "%a@ " Sexp.pp_hum chc;
                 KB.return ()
         ) >>= fun () ->
       KB.Object.create Theory.Program.cls
      ) 
      kb
  in
  match res with
  | Ok _ -> ()
  | Error _ -> failwith "KB error"



let () = Extension.declare @@ fun _ctxt ->
  (* decide_name_from_possible_name (); *)
  (* if Extension.Configuration.get ctxt herbrand_enabled
     then begin enable_herbrand ()(* ; enable_varset () *) end; 
     promise_chc ();
  *)
  Allvars.enable_varset ();
  enable_herbrand () ;
  let pp_chc =  Regular.Std.Data.Write.create ~pp:(pp_chc) () in

  Project.add_writer  ~ver:"1" "chc"
    ~desc:"dumps the chc" pp_chc;
  let pp_rule =  Regular.Std.Data.Write.create ~pp:(pp_rule) () in
    Project.add_writer  ~ver:"1" "rule"
    ~desc:"dumps z3 rules" pp_rule;
  Ok ()