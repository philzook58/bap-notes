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

(* I guess we could have equality based on instatiating the transformer *)
let wp_domain : (Sexp.t -> Var.t list -> Sexp.t) option KB.Domain.t = KB.Domain.optional
 ~inspect:(fun wp -> wp (Sexp.Atom "POST") [Var.create "ALLVARS" (Imm 32)]) 
 ~equal:(fun wp wp' -> true) "wp"



let eslot = KB.Class.property Theory.Semantics.cls "eff"
    ~package
    ~public:true
    wp_domain

let pslot = KB.Class.property Theory.Value.cls "val"
    ~package
    ~public:true
    domain

let chc = KB.Class.property Theory.Program.cls "chc-val"
    ~package
    ~public:true
    domain

let addr_size = 32

(*
Make weakest precondition function eslot
Add chc slot

label(addr, rhos) :- wp()

wp(goto(addr)) = label(addr, rho)

*)

(*
module AllVars : Theory.Core = struct
  let domain = KB.Domain.powerset (module Var) "vars"
  let all_vars = KB.Class.property Theory.Value.cls "allvars"
    ~package
    ~public:true
    domain
  let pure s cst = KB.Value.put all_vars (Theory.Value.empty s) cst
  include Theory.Empty
  let var v =
    let s = Theory.Var.sort v in
    KB.return @@ pure s (Var.Set.singleton (Var.reify v))
  
  (* module Minimal = struct

  end
  include Theory.Basic.Make(Minimal) *)
end
*)



module AllVars = struct
  include Theory.Empty
  (* type t = Sexp.t *)
  let domain = KB.Domain.powerset (module Var) ~inspect:Var.sexp_of_t "vars"

  let eslot = KB.Class.property Theory.Semantics.cls "allvars-eff"
    ~package
    ~public:true
    domain
  let pslot = KB.Class.property Theory.Value.cls "allvars-val"
    ~package
    ~public:true
    domain


  let pure s cst = KB.Value.put pslot (Theory.Value.empty s) cst
  let eff s cst = KB.Value.put eslot (Theory.Effect.empty s) cst
  let data = eff Theory.Effect.Sort.bot
  let ctrl = eff Theory.Effect.Sort.bot
  let ret = KB.return

  let psort = Theory.Value.sort
  let esort = Theory.Effect.sort

  let (>>->) x f =
    x >>= fun v ->
    let s = psort v in
    f s (KB.Value.get pslot v)

  let (>>|>) x f = x >>-> fun s v -> ret (f s v)

  let (>>=>) x f =
    x >>= fun v ->
    let s = esort v in
    f s (KB.Value.get eslot v)

  let empty = Theory.Value.empty
  let atom _ = Var.Set.empty

  let monoid_s s op x y =
    x >>-> fun _ x ->
    y >>|> fun _ y ->
   pure s @@ Var.Set.union x y
  let unary_s s op x = 
    x >>-> fun _ x -> ret@@pure s x
  let unary op x = 
    x >>-> fun s x -> ret@@pure s x
  let monoid op x y =
    x >>-> fun s x ->
    y >>|> fun _ y ->
    pure s @@ Var.Set.union x y

  module Minimal = struct
    let b0 = ret@@pure Theory.Bool.t (atom "#b0")
    let b1 = ret@@pure Theory.Bool.t (atom "#b1")

    let unk s = ret@@empty s

    let var v =
      let s = Theory.Var.sort v in
      ret@@pure s@@ Var.Set.singleton (Var.reify v)

    let let_ v x y =
      x >>-> fun _ x ->
      y >>|> fun s y ->
      pure s@@ Var.Set.add (Var.Set.union x y) (Var.reify v)

    let ite c x y =
      c >>-> fun _ c ->
      x >>-> fun s x ->
      y >>|> fun _ y -> 
      pure s@@ Var.Set.union_list [c; x; y]

    let inv = unary "bvnot"
    let and_ = monoid "bvand"
    let or_ = monoid "bvor"
    let int s x = ret@@pure s@@atom (Bitvec.to_string x)
    let msb x = unary_s Theory.Bool.t "msb" x
    let lsb x = unary_s Theory.Bool.t "lsb" x
    let neg x = unary "bvneg" x
    let not x = unary "bvnot" x
    let add x = monoid "bvadd" x
    let sub x = monoid "bvsub" x
    let mul x = monoid "bvmul" x
    let div x = monoid "bvdiv" x
    let sdiv x = monoid "s/" x
    let modulo x = monoid "mod" x
    let smodulo x = monoid "signed-mod" x
    let logand x = monoid "logand" x
    let logor x = monoid "logor" x
    let logxor x = monoid "logxor" x

    let genshift name fill x off =
      fill >>-> fun _ fill ->
      x >>-> fun s x ->
      off >>|> fun _ off ->
        pure s @@ Var.Set.union_list [fill; x; off]
      
    let shiftr x = genshift "shiftr" x
    let shiftl x = genshift "shiftl" x
    let sle x = monoid_s Theory.Bool.t "s<=" x
    let ule x = monoid_s Theory.Bool.t "<" x


    let cast s fill exp =
      fill >>-> fun _ fill ->
      exp >>|> fun s' x ->
      pure s (Var.Set.union fill x)

    let concat s xs =
      List.map xs ~f:(fun x -> x >>|> fun _ -> ident) |>
      KB.List.all >>| fun xs -> pure s @@ Var.Set.union_list xs

    let append s x y = monoid_s s "append" x y

    let load m x =
      m >>-> fun s m ->
      x >>|> fun _ x ->
      let s = Theory.Mem.vals s in
       pure s @@ Var.Set.union_list [m; x]

    let store m p x =
      m >>-> fun s m ->
      p >>-> fun _ p ->
      x >>|> fun _ x ->
        pure s @@ Var.Set.union_list [m; p; x]

    let nil = Theory.Effect.empty Theory.Effect.Sort.bot

    let perform eff = ret (Theory.Effect.empty eff)

    let set v x = x >>|> fun _ x ->
      data @@ Var.Set.add x (Var.reify v)

    let jmp x = x >>|> fun _ x -> ctrl x

    let goto dst =
      KB.collect Theory.Label.addr dst >>= function
      | Some dst ->
        ret@@ctrl@@ Var.Set.empty
      | None ->
        KB.Object.repr Theory.Program.cls dst >>= fun dst ->
        ret@@ctrl@@ Var.Set.empty

    let both s xs ys =
      ret@@eff s@@Var.Set.union_list [xs; ys]

    let seq xs ys =
      xs >>=> fun s xs ->
      ys >>=> fun _ ys ->
      both s xs ys

    let blk _ xs ys =
      xs >>=> fun _ xs ->
      ys >>=> fun _ ys ->
      both Theory.Effect.Sort.top xs ys

    let repeat cnd body =
      cnd >>-> fun _ cnd ->
      body >>=> fun s body ->
      ret@@eff s@@Var.Set.union_list [cnd; body]

    let branch cnd yes nay =
      cnd >>-> fun _ cnd ->
      yes >>=> fun s yes ->
      nay >>=> fun _ nay ->
        ret@@eff s@@Var.Set.union_list [cnd; yes; nay]
  end
  include Theory.Basic.Make(Minimal)
end


module Z3Helpers = struct
  let atom s = Sexp.Atom s
  

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
    let escape s =
      let s = String.substr_replace_all s ~pattern:"%" ~with_:"%%" in
      String.substr_replace_all s ~pattern:"#" ~with_:"%P"
    let unescape s = ()

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
    let svar' v = atom @@ escape @@ (Var.to_string v) (* I should escape though *)
    let z3_sort' (typ : typ) = 
      let bitvec n = utag (atom "BitVec") (atom @@ Int.to_string n) in
      match typ with
      | Imm n ->  bitvec n
      | Mem (addr_size, size) -> 
         let range_size = Size.in_bits size in
         let dom_size = Size.in_bits addr_size in
         app "Array" [bitvec dom_size; bitvec range_size]
      | _ -> failwith (sprintf "unimplemented z3_sort %a" Type.pps typ)
    let var_sorts' vars : Sexp.t list =
        List.map vars ~f:(fun v ->
            list [svar' v; z3_sort' (Var.typ v)])
    let var_sorts vars : Sexp.t =
      list @@ var_sorts' vars
end

module Herbrand : Theory.Core = struct
  (* type t = Sexp.t *)
  include Theory.Empty
  open Z3Helpers

  (* collect sequence of 
  [ ; ; ; ] and Set of variables updated?
  set of variables updated * transition_relation sexp.t
  
  *)
  let pure s cst = KB.Value.put pslot (Theory.Value.empty s) (Some cst)
  let eff s cst = KB.Value.put eslot (Theory.Effect.empty s) (Some cst)
  let data = eff Theory.Effect.Sort.bot
  let ctrl = eff Theory.Effect.Sort.bot
  let ret = KB.return

(*
  let sort_subscript (s : 'a Theory.Value.Sort.t) : string = 
    let s = Theory.Value.Sort.forget s in
    match Theory.Bitv.refine s with
    | Some s -> Int.to_string (Theory.Bitv.size s) (* utag (atom "BitVec") (atom @@ Int.to_string (Theory.Bitv.size s)) *)
    | None -> 
    match Theory.Bool.refine s with
    | Some _ -> "Bool"
    | None -> "failure to refine z3 sort"
*)



(*
  let rho_sorts =
    let forget = Theory.Value.Sort.forget in
    [forget Theory.Bool.t] 
    @
    (List.map ~f:(fun i -> forget @@ Theory.Bitv.define i) [32])
  let rho_s (s : 'a Theory.Value.Sort.t) : Sexp.t =
    atom @@ "rho_" ^ (sort_subscript s)
  let rho_new_s  (s : 'a Theory.Value.Sort.t) : Sexp.t =
    atom @@ "rho_new_" ^ (sort_subscript s)
  let rho_temp_s  (s : 'a Theory.Value.Sort.t) : Sexp.t =
    atom @@ "rho_temp_" ^ (sort_subscript s)
  *)

      


  let psort = Theory.Value.sort
  let esort = Theory.Effect.sort

  let (>>->) x f =
    x >>= fun v ->
    let s = psort v in
    f s (KB.Value.get pslot v)

  let (>>|>) x f = x >>-> fun s v -> ret (f s v)

  let (>>->?) x f =
    x >>= fun v ->
    let s = psort v in
    match KB.Value.get pslot v with
    | None -> ret (Theory.Value.empty s)
    | Some v -> f s v


  let (>>|>?) x f = x >>->? fun s v -> ret (f s v)

  let (>>=>) x f =
    x >>= fun v ->
    let s = esort v in
    f s (KB.Value.get eslot v)

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
    let b0 = ret@@pure Theory.Bool.t (atom "#b0")
    let b1 = ret@@pure Theory.Bool.t (atom "#b1")

    let unk s = ret@@empty s

    let var v =
      let s = Theory.Var.sort v in
      (* Variable names in bap can be unacceptable characters for smtlib, so we use the string theory as labels *)
      (* alternative: use an escape character. % for example. and then % -> %% *)
      (* ret@@pure s@@ list [atom "select" ; rho_s s; svar v] *)
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
      (*unary_s Theory.Bool.t "msb" x *)
      (* x >>->? fun _ x ->
      ret @@ pure Theory.Bool.t @@ fun _ _ -> 
    atom "true"; 
    atom "false"] *)
      
     (* *)
(*    let lsb x = unary_s Theory.Bool.t "lsb" x *)
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
          let pad = z3_const (Theory.Bitv.define Int.(newsize - size)) Bitvec.zero in
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
      let s = Theory.Var.sort v in
     (* let rho = rho_s s in
      let rho_new = (rho_new_s s) in *)
      match x with
      | None -> nil
      | Some x -> data@@
       fun post _ -> 
        list [atom "let"; 
        list [list [svar v; x]];
              post]
        (* list [atom "let"; 
        list [rho; list [atom "store"; rho; (svar v); x]];
        post] *)
      (* app "=" [
          rho_new;
          list [atom "store"; rho; (svar v); x]
        ] *)

    
    let jmp x = x >>|> fun _ x -> match x with
      | None -> nil
      | Some x -> ctrl@@ fun post all_vars -> 
        let all_vars = List.map ~f:svar' all_vars in
        list [atom "and"; 
              list (atom "label" :: x :: all_vars);
              post]

      (*
      WP:
      Var.Set.t -> Sexp.t -> Sexp.t
      Because I need to knwo the ambient W vector
      *)

    let goto dst =
      KB.collect Theory.Label.addr dst >>= function
      | Some dst ->
        ret@@ctrl@@ fun post vars -> app "label" (atom (z3_const (Theory.Bitv.define addr_size) dst) :: List.map ~f:svar' vars)
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
        (* Relation composition. I don't know if z3 is smart enough to chew on this. Maybe it is. *)
        (* let rhos = List.map rho_sorts ~f:(fun s -> 
          let rho = rho_s s in
          let rho_new = rho_new_s s in
          let rho_temp = rho_temp_s s in
          (rho, rho_temp, rho_new, s)) in
          let rho_temp_def = List.map rhos ~f:(fun (_,rho_temp,_,s) -> 
            list [rho_temp ; list [atom "Array"; atom "String" ;z3_sort s]]
            ) in
          let xs = list [atom "let"; list @@ List.map rhos ~f:(fun (_,rho_temp,rho_new,_) -> 
            list [rho_new; rho_temp]
            ); xs] in
          let ys = list [atom "let"; list @@ List.map rhos ~f:(fun (rho,rho_temp,_,_) -> 
              list [rho; rho_temp]
              ); ys] in
          list [atom "exists" ; list rho_temp_def;
            list [atom "and"; xs; ys] ] *)
 
        let seq xs ys =
          xs >>=> fun s xs ->
          ys >>=> fun _ ys ->
          both s xs ys
          
    
        let blk label xs ys =
          xs >>=> fun _ xs ->
          ys >>=> fun _ ys ->
         (* fun s vars -> list [
            atom "and";
           (wpdata (wpctrl s));
           [forall  ;atom "=>" ; atom ""]
          ] "(forall %a (=> (label %a %a) %a) )" pp_varset varset pp_label label pp_varset vars
*)
          both Theory.Effect.Sort.top xs ys (* >>=>? fun s wp ->
              ret@@eff s@@ fun post vars -> 
            let all_vars = List.map ~f:svar' vars in
            let bind_vars = List.map vars ~f:(fun v ->
              list [svar' v ; z3_sort' (Var.typ v) ]
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
    (*
      let mk_cast name s x =
        x >>|> fun s' x -> match x with
        | None -> empty s
        | Some x ->
          if Theory.Value.Sort.same s s'
          then pure s x
          else pure s@@app name [
              atom@@sprintf "%d" (Theory.Bitv.size s);
              x
            ]
    
      let high s = mk_cast "high" s
      let low s = mk_cast "low" s
      let signed s = mk_cast "signed" s
      let unsigned s = mk_cast "unsigned" s
    
      let extract s lo hi x =
        lo >>-> fun _ lo ->
        hi >>-> fun _ hi ->
        x >>|> fun _ x ->
        match lo,hi,x with
        | Some lo, Some hi, Some x ->
          pure s@@app "extract" [lo; hi; x]
        | _ -> empty s
    
      let loadw s dir mem ptr =
        dir >>-> fun _ dir ->
        mem >>-> fun _ mem ->
        ptr >>|> fun _ ptr ->
        match dir,mem,ptr with
        | Some dir, Some mem, Some ptr ->
          pure s@@app "loadw" [
            atom@@sprintf "%d" (Theory.Bitv.size s);
            dir;
            mem;
            ptr
          ]
        | _ -> empty s
    
      let storew dir mem ptr exp =
        dir >>-> fun _ dir ->
        mem >>-> fun s mem ->
        ptr >>-> fun _ ptr ->
        exp >>|> fun _ exp ->
        match Option.all [dir; mem; ptr; exp] with
        | Some args -> pure s@@app "storew" args
        | _ -> empty s
    
      let mk_shift name x m =
        x >>->? fun s x ->
        m >>|> fun _ -> function
        | None -> empty s
        | Some m -> pure s@@app name [x; m]
    
      let arshift x = mk_shift "arshift" x
      let rshift x = mk_shift "rshift" x
      let lshift x = mk_shift "lshift" x
      let eq x = monoid_s Theory.Bool.t "=" x
      let neq x = monoid_s Theory.Bool.t "/=" x
      let slt x = monoid_s Theory.Bool.t "s<" x
      let ult x = monoid_s Theory.Bool.t "<" x
      let sgt x = monoid_s Theory.Bool.t "s>" x
      let ugt x = monoid_s Theory.Bool.t ">" x
      let sge x = monoid_s Theory.Bool.t "s>=" x
      let uge x = monoid_s Theory.Bool.t ">=" x
    
      let asort s =
        atom@@Format.asprintf "%a" Theory.Value.Sort.pp (Theory.Value.Sort.forget s)
    
    
      let wellknown = Theory.IEEE754.[
          binary16,  ":b16";
          binary32,  ":b32";
          binary64,  ":b64";
          binary80,  ":b80";
          binary128, ":b128";
          decimal32, ":d32";
          decimal64, ":d64";
          decimal128, ":d128";
        ]
    
      let format s =
        let s = Theory.Value.Sort.forget s in
        match Theory.Float.(refine s) with
        | None -> asort s
        | Some s ->
          List.find_map wellknown ~f:(fun (par,name) ->
              let s' = Theory.IEEE754.Sort.define par in
              if Theory.Value.Sort.same s s'
              then Some (atom name)
              else None) |> function
          | Some s -> s
          | None -> asort s
    
    
    
      let float s x =
        x >>|> fun _ x -> match x with
        | None -> empty s
        | Some x -> pure s@@app "float" [format s; x]
    
      let fbits x =
        x >>|> fun s x ->
        let s = Theory.Float.bits s in
        match x with
        | None -> empty s
        | Some x -> pure s@@app "fbits" [x]
    
      let is_finite x = unary_s Theory.Bool.t "is-finite" x
      let is_nan x = unary_s Theory.Bool.t "is-nan" x
      let is_inf x = unary_s Theory.Bool.t "is-inf" x
      let is_fzero x = unary_s Theory.Bool.t "is-fzero" x
      let is_fpos x = unary_s Theory.Bool.t "is-fpos" x
      let is_fneg x = unary_s Theory.Bool.t "is-fneg" x
    
      let rmode s = ret@@pure Theory.Rmode.t @@ atom s
      let rne = rmode ":rne"
      let rna = rmode ":rna"
      let rtp = rmode ":rtp"
      let rtn = rmode ":rtn"
      let rtz = rmode ":rtz"
      let requal = eq
    
      let mk_fcast name s m x =
        m >>-> fun _ m ->
        x >>|> fun _ x ->
        match m,x with
        | Some m, Some x -> pure s@@app name [m;x]
        | _ -> empty s
    
      let cast_float s = mk_fcast "cast-float" s
      let cast_sfloat s = mk_fcast "cast-sfloat" s
      let cast_int s = mk_fcast "cast-int" s
      let cast_sint s = mk_fcast "cast-sint" s
    
      let fneg x = unary "fneg" x
      let fabs x = unary "fabs" x
    
      let monoid_f name m x y =
        x >>->? fun s x ->
        y >>->? fun _ y ->
        m >>|> fun _ m ->
        match m with
        | None -> empty s
        | Some m -> pure s@@app name [m; x; y]
    
      let unary_f name m x =
        x >>->? fun s x ->
        m >>|> fun _ m ->
        match m with
        | None -> empty s
        | Some m -> pure s@@app name [m; x]
    
      let ternary_f name m x y z =
        x >>->? fun s x ->
        y >>->? fun _ y ->
        z >>->? fun _ z ->
        m >>|> fun _ m ->
        match m with
        | None -> empty s
        | Some m -> pure s@@app name [m; x; y; z]
    
      let binary_fi name m f x =
        f >>->? fun s f ->
        m >>-> fun _ m ->
        x >>|> fun _ x ->
        match m,x with
        | Some m, Some x -> pure s@@app name [m; f; x]
        | _ -> empty s
    
    
      let fadd m = monoid_f "+." m
      let fsub m = monoid_f "-." m
      let fmul m = monoid_f "*." m
      let fdiv m = monoid_f "/." m
      let fmodulo m = monoid_f "mod." m
      let fsqrt m = unary_f "fsqrt" m
      let fround m = unary_f "fround" m
      let fmad m = ternary_f "fmad" m
      let fsucc x = unary "fsucc" x
      let fpred x = unary "fpred" x
      let forder x = monoid_s Theory.Bool.t "forder" x
    
      let fconvert s m x =
        m >>-> fun _ m ->
        x >>|> fun _ x ->
        match m,x with
        | Some m, Some x -> pure s@@app "fconvert" [
            format s; m; x
          ]
        | _ -> empty s
    
      let pow m = monoid_f "pow" m
      let hypot m = monoid_f "hypot" m
    
      let rsqrt m = unary_f "rsqrt" m
      let exp m = unary_f "exp" m
      let expm1 m = unary_f "expm1" m
      let exp2 m = unary_f "exp2" m
      let exp2m1 m = unary_f "exp2m1" m
      let exp10 m = unary_f "exp10" m
      let exp10m1 m = unary_f "exp10m1" m
      let log m = unary_f "log" m
      let log2 m = unary_f "log2" m
      let log10 m = unary_f "log10" m
      let logp1 m = unary_f "logp1" m
      let log2p1 m = unary_f "log2p1" m
      let log10p1 m = unary_f "log10p1" m
      let sin m = unary_f "sin" m
      let cos m = unary_f "cos" m
      let tan m = unary_f "tan" m
      let sinpi m = unary_f "sinpi" m
      let cospi m = unary_f "cospi" m
      let atanpi m = unary_f "atanpi" m
      let atan2pi m = monoid_f "atan2pi" m
      let asin m = unary_f "asin" m
      let acos m = unary_f "acos" m
      let atan m = unary_f "atan" m
      let atan2 m = monoid_f "atan2" m
      let sinh m = unary_f "sinh" m
      let cosh m = unary_f "cosh" m
      let tanh m = unary_f "tanh" m
      let asinh m = unary_f "asinh" m
      let acosh m = unary_f "acosh" m
      let atanh m = unary_f "atanh" m
    
      let compound m = binary_fi "compound" m
      let rootn m = binary_fi "rootn" m
      let pown m = binary_fi "pown" m *)


end


let promise_chc () = 
  let open Z3Helpers in
  KB.promise chc (fun label ->
    KB.collect Theory.Label.addr label >>= fun addr ->
    KB.collect Theory.Semantics.slot label >>= fun sem ->
      let (let*) x f = Option.bind x ~f in
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
let herbrand_enabled = Extension.Configuration.parameter
    Extension.Type.(bool =? false) "enable"
    ~as_flag:true
    (* ~aliases:["herbrand"; "debug"] *)

let enable_herbrand () =
  Theory.declare
    ~provides:herbrand_provides
    ~desc:"provides smt interpretation"
    ~package
    ~name:"syntax" (KB.return (module Herbrand : Theory.Core))

let enable_varset () =
  Theory.declare
    ~provides:herbrand_provides
    ~desc:"Set of all variables in expression"
    ~package
    ~name:"varset" (KB.return (module AllVars : Theory.Core))

let pp_chc ppf proj =
  let open Z3Helpers in
  let kb = Toplevel.current () in
  let res = KB.run Theory.Program.cls 
  (KB.objects Theory.Program.cls >>= fun progs ->
  let* allvars = KB.Seq.fold progs ~init:Var.Set.empty 
    ~f:(fun vars prog -> 
      KB.collect Theory.Semantics.slot prog >>= fun sem ->
      let vars' = KB.Value.get AllVars.eslot sem in
      KB.return @@ Var.Set.union vars vars'
      ) 
  in
  let allvars = Var.Set.to_list allvars in
  (* Format.fprintf ppf "#define ALLVARS"; *)
  let sorts = list @@ utag (atom "BitVec") (atom (string_of_int addr_size)) :: List.map ~f:(fun v -> z3_sort' (Var.typ v)) allvars in
  Format.fprintf ppf "(declare-fun label %a Bool)@ " Sexp.pp_hum sorts;
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
    let all_vars = List.map ~f:Z3Helpers.svar' allvars in
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
    let fallthrough = app "label" (atom fall_addr :: all_vars) in
    let bind_vars = var_sorts allvars in
    let chc =  app "assert" [app "forall"
                [ bind_vars;
                  app "=>"
                    [app "label" (atom z3_addr :: all_vars ) ;
                    wp fallthrough allvars]]]
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
  


let () = Extension.declare @@ fun ctxt ->
  (* decide_name_from_possible_name (); *)
  (* if Extension.Configuration.get ctxt herbrand_enabled
  then begin enable_herbrand ()(* ; enable_varset () *) end; *)
  enable_varset ();
  enable_herbrand () ;
  promise_chc ();
  let pp_chc =  Regular.Std.Data.Write.create ~pp:(pp_chc) () in
  Project.add_writer  ~ver:"1" "chc"
  ~desc:"dumps the chc" pp_chc;
  Ok ()