open Core_kernel
open Bap.Std
open Bap_core_theory
open KB.Let

module T = Theory

module Toy_implementation : T.Core = struct

  include T.Empty

  (* Not actually sure to what degree the persistent and public field matter *)
  let comment_slot = KB.Class.property ~public:true ~persistent:KB.Persistent.string T.Effect.cls "comment" KB.Domain.string

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

let () = let theory = KB.return (module Toy_implementation : T.Core) in
         T.declare ~package:"toy" ~name:"toy" theory;