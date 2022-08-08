
open Bap.Std
open Core
let pp_tid ppf tid = 
  Format.fprintf ppf "\"\"%a\"\"" Tid.pp tid

let pp_opt f ppf opt =
  match opt with
  | Some x -> f ppf x
  | None -> Format.fprintf ppf "nil"


let pp_def ppf def =
  let var = Def.lhs def in
  let tid = Term.tid def in
  let rhs = Def.rhs def in
  Format.fprintf ppf
    "[%a,%a,%a]" pp_tid tid Ppbil.pp_var var Ppbil.Exp.pp rhs

let pp_dst ppf dst =
  match Jmp.resolve dst with
  | First tid  -> Format.fprintf ppf "$Resolved(%a)" pp_tid tid
  | Second v -> 
    let exp = Bap_knowledge.Knowledge.Value.get Exp.slot v in
    (* TODO. What the hell is this. *)
    Format.fprintf ppf "$Indirect(%a,0)" Ppbil.Exp.pp exp

let pp_jmp ppf jmp =
  let tid = Term.tid jmp in
  let cnd = Jmp.cond jmp in
  let dst = Jmp.dst jmp in
  let alt = Jmp.alt jmp in
  Format.fprintf ppf
  "[%a,%a,%a,%a]" pp_tid tid Ppbil.pp_exp cnd (pp_opt pp_dst) dst (pp_opt pp_dst) alt


let pp_phi ppf phi =
  failwith "unimplemented phi"


let pp_list f ppf xs : unit =
  let rec worker ppf xs = 
  match xs with
  | [] -> Format.fprintf ppf "nil"
  | x :: xs -> 
    Format.fprintf ppf "[%a,%a]" f x worker xs
  in 
  worker ppf xs

let pp_jmps = pp_list pp_jmp
let pp_defs = pp_list pp_def
(* let pp_phi = pp_list pp_phi *)
let pp_blk ppf blk =
  let defs = Seq.to_list @@ Term.enum def_t blk in
  let jmps = Seq.to_list @@ Term.enum jmp_t blk in
  let phis = Seq.to_list @@ Term.enum phi_t blk in
  let tid = Term.tid blk in
  Format.fprintf ppf "[%a, %a, %a]" pp_tid tid pp_defs defs pp_jmps jmps

let pp_sub ppf sub =
  let blks = Term.enum blk_t sub in
  Seq.iter blks ~f:(fun blk ->
    Format.fprintf ppf  "%a\n" pp_blk blk
    )