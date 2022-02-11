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
let domain = KB.Domain.powerset (module Var) ~inspect:Var.sexp_of_t "vars"

let eslot = KB.Class.property Theory.Semantics.cls "allvars-eff"
  ~package
  ~public:false
  domain
let pslot = KB.Class.property Theory.Value.cls "allvars-val"
  ~package
  ~public:false
  domain

module AllVars : Theory.Core = struct
  include Theory.Empty
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

let enable_varset () =
  Theory.declare
    ~provides:herbrand_provides
    ~desc:"Set of all variables in expression"
    ~package
    ~name:"varset" (KB.return (module AllVars : Theory.Core))