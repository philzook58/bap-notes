open Core_kernel
open Bap.Std
open Bap_core_theory
open KB.Let

module T = Theory

module Toy_implementation : T.Core = struct

  include T.Empty

  (* Not actually sure to what degree the persistent and public field matter 
  Ivan: 
  The ~persistent type-class instance makes your property persistent so that it is stored
  in the cache (and therefore loaded back), so indeed, if you wouldn't specify it, 
  then you will see the property only on the first run and won't see it afterward 
  when the knowledge base is loaded from the cache. Provided that the cache system is enabled.

  *)
  type initial_core = Blk of (initial_core option) * (initial_core option)
        | Seq of (initial_core option) * (initial_core option)
        | Set [@@deriving equal, compare, sexp, hash]
  let icore_domain = KB.Domain.optional 
    ~inspect:sexp_of_initial_core ~equal:equal_initial_core "initial_core"
  let icore_slot = KB.Class.property ~public:true (* ~persistent:KB.Persistent.string *) 
      T.Effect.cls ~package:"toy" 
      ~desc:"A slot to reflect the final Core theory into an initial data type for inspection. What order do Seq, Blk, Set happen?"
      "initial_core" icore_domain

    let nop = Theory.Effect.empty Theory.Effect.Sort.bot
    let blk (label : T.label) (data : T.data T.eff) (ctrl : T.ctrl T.eff)
      : unit T.eff =
    let* data = data in
    let icore = KB.Value.get icore_slot data in
    KB.return @@ KB.Value.put icore_slot nop (Some (Blk (icore, None)))
   
    let seq eff1 eff2
      : 'a T.eff =
    let* eff1 = eff1 in
    let* eff2 = eff2 in
    let icore1 = KB.Value.get icore_slot eff1 in
    let icore2 = KB.Value.get icore_slot eff2 in
    KB.return @@ KB.Value.put icore_slot nop (Some (Seq (icore1,icore2)))

    let set a b =
    KB.return @@
    KB.Value.put icore_slot nop (Some Set)
end

let () =
  Bap_main.Extension.declare (fun _ctx ->
  let theory = KB.return (module Toy_implementation : T.Core) in
         T.declare ~package:"toy" ~name:"icore_reflect" theory;
         Ok ())