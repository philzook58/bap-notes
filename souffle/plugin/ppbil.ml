(* https://github.com/BinaryAnalysisPlatform/bap/blob/master/lib/bap_types/bap_bil_adt.ml *)
open Core_kernel[@@warning "-D"]
open Regular.Std
open Bap.Std
(* open Bap_bil *)
module Word = Bitvector


let pr ch fms = Format.fprintf ch fms

let pp_word ch word =
  pr ch "$Word(%a,%d)"
    Word.pp_dec word
    (Word.bitwidth word)

let pp_endian ch = function
  | BigEndian -> pr ch "$BigEndian"
  | LittleEndian -> pr ch "$LittleEndian"

let pp_size ch size =
  pr ch "%d" (Size.in_bits size)

let pp_sexp sexp ch x =
  pr ch "%a" Sexp.pp (sexp x)

module Var = struct
  let pp_ty ch = function
    | Type.Imm n -> pr ch "$Imm(%d)" n
    | Type.Mem (n,m) -> pr ch "$Mem(%a,%a)" pp_size n pp_size m
    | Type.Unk -> pr ch "$Unk()"

  let pp_var ch v =
    pr ch "$Var(\"\"%a\"\",%a)" Var.pp v  pp_ty Var.(typ v)

end

module Exp = struct
  open Bil
  open Exp
  open Var

  let rec pp ch = function
    | Load (x,y,e,s) ->
      pr ch "$Load(%a,%a,%a,%a)" pp x pp y pp_endian e pp_size s
    | Store (x,y,z,e,s) ->
      pr ch "$Store(%a,%a,%a,%a,%a)" pp x pp y pp z pp_endian e pp_size s
    | BinOp (op,x,y) ->
      pr ch "$BinOp(\"\"%a\"\",%a,%a)" (pp_sexp sexp_of_binop) op pp x pp y
    | UnOp (op,x) ->
      pr ch "$UnOp(\"\"%a\"\",%a)" (pp_sexp sexp_of_unop) op pp x
    | Var v -> pr ch "$EVar(%a)" pp_var v
    | Int w -> pr ch "$Int(%a)" pp_word w
    | Cast (ct,sz,ex) ->
      pr ch "$Cast(\"\"%a\"\",%d,%a)" (pp_sexp sexp_of_cast) ct sz pp ex
    | Let (v,e1,e2) -> pr ch "$Let(%a,%a,%a)" pp_var v pp e1 pp e2
    | Unknown (s,t) -> pr ch "$Unknown(%S,%a)" s pp_ty t
    | Ite (e1,e2,e3) -> pr ch "$Ite(%a,%a,%a)" pp e1 pp e2 pp e3
    | Extract (n,m,e) -> pr ch "$Extract(%d,%d,%a)" n m pp e
    | Concat (e1,e2) -> pr ch "$Concat(%a,%a)" pp e1 pp e2

end

module Stmt = struct
  open Bil
  open Stmt
  open Var
  let rec pp ch = function
    | Move (v,e) -> pr ch "$Move(%a,%a)" pp_var v Exp.pp e
    | Jmp e -> pr ch "$Jmp(%a)" Exp.pp e
    | Special s -> pr ch "$Special(\"\"%s\"\")" s
    | While (e,ss) -> pr ch "$While(%a, (%a))" Exp.pp e pps ss
    | If (e,xs,ys) -> pr ch "$If(%a, (%a), (%a))" Exp.pp e pps xs pps ys
    | CpuExn n -> pr ch "$CpuExn(%d)" n
  and pps ch = function
    | []  -> pr ch "nil"
    | s :: ss -> pr ch "[%a, %a]" pp s pps ss
end

module Bil = struct
  let pp ppf bil = pr ppf "\"%a\"" Stmt.pps bil
end


let pp_stmt = Stmt.pp
let pp_exp = Exp.pp
let pp_var = Var.pp_var

let add_souffle_writers () =
  let desc = "Abstract Data Type pretty printing format" in
  let ver = "1" and name = "souffle" in
  let create pp = Data.Write.create ~pp  () in
  create Var.pp_var |> Bap.Std.Var.add_writer ~desc ~ver name;
  create Exp.pp  |> Bap.Std.Exp.add_writer ~desc ~ver name;
  create Stmt.pp |> Bap.Std.Stmt.add_writer ~desc ~ver name;
  create Bil.pp  |> Bap.Std.Bil.add_writer ~desc ~ver name