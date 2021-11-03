open Core_kernel
open Bap.Std
open Bap_core_theory
open KB.Let

module T = Theory

module Toy_implementation : T.Core = struct

  include T.Empty

  (* Not actually sure to what degree the persistent and public field matter 
  The ~persistent type-class instance makes your property persistent so that it is stored in the cache (and therefore loaded back), so indeed, if you wouldn't specify it, then you will see the property only on the first run and won't see it afterward when the knowledge base is loaded from the cache. Provided that the cache system is enabled.

  *)
  let comment_slot = KB.Class.property ~public:true (* ~persistent:KB.Persistent.string *) T.Effect.cls ~package:"toy" "comment" KB.Domain.string

  let blk (label : T.label) (data : T.data T.eff) (ctrl : T.ctrl T.eff)
      : unit T.eff =
    let nop = Theory.Effect.empty Theory.Effect.Sort.bot in
    KB.return @@
    KB.Value.put comment_slot nop "hello, world"

    let seq a b
      : 'a T.eff =
    let nop = Theory.Effect.empty Theory.Effect.Sort.bot in
    KB.return @@
    KB.Value.put comment_slot nop "hello, world"

    let set a b =
    let nop = Theory.Effect.empty Theory.Effect.Sort.bot in
    KB.return @@
    KB.Value.put comment_slot nop "hello, world"

end

let () =
  Bap_main.Extension.declare (fun _ctx ->
  let theory = KB.return (module Toy_implementation : T.Core) in
         T.declare ~package:"toy" ~name:"toy" theory;
         Ok ())