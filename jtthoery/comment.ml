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
  let comment_slot = KB.Class.property ~public:true (* ~persistent:KB.Persistent.string *) 
      T.Effect.cls ~package:"toy" 
      ~desc:"An example slot put into the knowledge base. Will be populated with the string 'hello world'"
      "comment" KB.Domain.string

    let blk (label : T.label) (data : T.data T.eff) (ctrl : T.ctrl T.eff)
      : unit T.eff =
    let* data = data in
    let nop = Theory.Effect.empty Theory.Effect.Sort.bot in
    (* KB.return data *)
    let comment = KB.Value.get comment_slot data in
    KB.return @@ KB.Value.put comment_slot nop "helloblock"
  
    (*

    KB.return @@ nop

    Ok sometimes instructions translate to multiple blocks. Is that right?
    Or perhaps a sequence is laweays wrapped in a block?

   *)
   
    let seq eff1 eff2
      : 'a T.eff =
    let* eff1 = eff1 in
    let* eff2 = eff2 in
    let nop = Theory.Effect.empty Theory.Effect.Sort.bot in
    KB.return @@ KB.Value.put comment_slot eff1 "helloseq" 
    (* KB.return eff1  *)
(*
    let set a b =
    let nop = Theory.Effect.empty Theory.Effect.Sort.bot in
    KB.return @@
    KB.Value.put comment_slot nop "helloset"
*)
end

let () =
  Bap_main.Extension.declare (fun _ctx ->
  let theory = KB.return (module Toy_implementation : T.Core) in
         T.declare ~package:"toy" ~name:"toy" theory;
         Ok ())