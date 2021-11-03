open Bap_knowledge.Knowledge
open Syntax
open Bap_core_theory
open Core_kernel
(* let () =
  Bap_main.Extension.declare (fun _ctx ->  
Theory.declare ~name:"my-constant-tracker" @@
  (((Theory.instance ~requires:["bap.std:constant-tracker"] ()) >>=
  Theory.require) >>|
  fun (module Base) : Theory.core -> (module struct
    include Base
    let add x y =
      Printf.printf "add is called!\n%!";
      add x y
  end
  ))
  *)
module SmtLib = struct
  let atom s = Sexp.Atom s
  let list l = Sexp.List l
  let var v = Sexp.Atom (Theory.Var.name v)
  let unk sort = failwith "unknown"
  let let_ v exp body = list [atom "let"; list [ list [ v; exp] ]; body]
  let ite c x y = list [atom "ite"; ]

  let b0 = atom "true" (*  "#b0" *)
  let b1 = atom "false" (*  "#b1" *)
  let inv x = list [atom "not"; x]
  let true_ = atom "true"

  let binop s x y = list [atom s; x ; y]
  let unop s x = list [atom s; x]
  let and_ = binop "and"
  let or_ = binop "or"


  let not = unop "bvneg"
  let add = binop "bvadd"
  let sub = binop "bvsub"
  let mul = binop "bvmul"
  let logor = binop "bvor"
  let lognot = binop "bvnot"

  let ilit i = atom (string_of_int i)

  let extract i j x = list [list [atom "_"; atom "extract"; ilit i ; ilit j]; x]
  let msb ~size x = 
    extract (size - 1) (size - 1) x
  let lsb ~size x = extract 0 0 x

(*
(simplify (bvadd #x07 #x03)) ; addition
(simplify (bvsub #x07 #x03)) ; subtraction
(simplify (bvneg #x07)) ; unary minus
(simplify (bvmul #x07 #x03)) ; multiplication
(simplify (bvurem #x07 #x03)) ; unsigned remainder
(simplify (bvsrem #x07 #x03)) ; signed remainder
(simplify (bvsmod #x07 #x03)) ; signed modulo
(simplify (bvshl #x07 #x03)) ; shift left
(simplify (bvlshr #xf0 #x03)) ; unsigned (logical) shift right
(simplify (bvashr #xf0 #x03)) ; signed (arithmetical) shift right

(simplify (bvor #x6 #x3))   ; bitwise or
(simplify (bvand #x6 #x3))  ; bitwise and
(simplify (bvnot #x6)) ; bitwise not
(simplify (bvnand #x6 #x3)) ; bitwise nand
(simplify (bvnor #x6 #x3)) ; bitwise nor
(simplify (bvxnor #x6 #x3)) ; bitwise xnor

*)

end

(* https://github.com/draperlaboratory/VIBES/blob/83b43290b39d0c2274ec8ac24246de735e8ca264/lib/src/arm_gen.ml *)

(*
KB.Value is different from Theory.Value btw



*)
let sexp_domain = KB.Domain.optional ~inspect:(fun x -> x) ~equal:Sexp.equal "sexp"
let smt_pure  : (Theory.Value.cls, Sexp.t option) slot =
  KB.Class.property Theory.Value.cls "smt-pure" sexp_domain

(* I guess we could have equality based on instatiating the transformer *)
let wp_domain : (Sexp.t -> Sexp.t) option domain = KB.Domain.optional ~inspect:(fun wp -> wp SmtLib.true_) ~equal:(fun _ _ -> false) "wp"

let smt_eff : (Theory.Effect.cls, (Sexp.t -> Sexp.t) option) slot =
KB.Class.property Theory.Effect.cls "smt-eff" wp_domain


let (let-) v f =
  KB.(>>=) v
    (fun v ->
      match KB.Value.get smt_pure v with
      | None ->
          let v_str = Format.asprintf "%a" KB.Value.pp v in
          failwith v_str
      | Some v -> f v)
let binop op = fun x y -> 
  x >>= fun z -> let sort = Theory.Value.sort z in
  let- x = x in
  let- y = y in
  let z = Theory.Value.empty sort in
  KB.return @@ KB.Value.put smt_pure z (Some (op x y))
(*
Core theory
Finally tagless : fine
Extensible reords : uhh. I don't understand this really but not a bnig problem persay. KB.value are extensbile records
KB monad : A state monad over the extensible records?


Wait these are cpmcrete types. How is this even finally tagless?
*)

module SmtLib_Core : Theory.Core = struct
  include Theory.Empty (* search bap gitter for this *)
  module S = SmtLib
  let var (x : 'a Theory.var) :  'a Theory.pure = 
    let sort = Theory.Var.sort x in
    let z = Theory.Value.empty sort in
    KB.return @@ KB.Value.put smt_pure z (Some (S.var x))
  let add (x : 's Theory.bitv) (y : 's Theory.bitv) : 's Theory.bitv = 
    x >>= fun z -> let sort = Theory.Value.sort z in
    let- x = x in (* |> Option.value_exn in *)
    (* let x = KB.Value.get smt_pure x in *)
    let- y = y in (* KB.Value.get smt_pure y |> Option.value_exn in *)
    let z = Theory.Value.empty sort in
    KB.return @@ KB.Value.put smt_pure z (Some (S.add x y))
   (*  let and_ = binop S.and_
    let or_ = binop S.or_
    let sub_ = binop S.sub
    let mul = binop S.mul
*)

  let set (v : 'a Theory.var) (x : 'a Theory.pure) : Theory.data Theory.eff =
    let open SmtLib in
    let- x = x in
    let wp_trans = Some (fun post -> let_ (var v) x post) in
    let z = Theory.Effect.empty (Theory.Effect.Sort.data "set") in
    KB.return @@ KB.Value.put smt_eff z wp_trans




  (* Theory.Basic.Make(Something that is Miniaml) *)
  (*
  let atom s = Sexp.Atom s
  let list l = Sexp.List l
  let var v = Sexp.Atom (Var.name v)
  let unk sort = failwith "unknown"
  let let_ v exp body = list [atom "let"; list [ list [ v; exp] ]; body]
  let ite c x y = list [atom "ite"; ]

  let b0 = atom "true"
  let b1 = atom "false"
  let inv x = list [atom "not"; x] *)
end

let () =   Bap_main.Extension.declare (fun _ctx ->
  Theory.declare ~name:"smtlib" (KB.return (module SmtLib_Core : Theory.Core)))