module Toy_implementation : T.Core = struct

  include T.Empty

  let seq eff1 eff2 =
    Format.printf "SEQ===========\n";
    let* raw_eff1 = eff1 in
    let bil_of_eff1 = KB.Value.get Bil.slot raw_eff1 in
    Format.printf "-- -- BIL of eff 1: %s\n" (Bil.to_string bil_of_eff1);
    let* raw_eff2 = eff2 in
    let bil_of_eff2 = KB.Value.get Bil.slot raw_eff2 in
    Format.printf "-- -- BIL of eff 2: %s\n" (Bil.to_string bil_of_eff2);
    seq eff1 eff2

  let blk (label : T.label) (data : T.data T.eff) (ctrl : T.ctrl T.eff)
      : unit T.eff =
    Format.printf "BLK==========\n";
    let* name = KB.collect T.Label.name label in
    let name_str = Option.value_map name ~default:"none" ~f:(fun x -> x) in
    Format.printf "-- -- Name: %s\n" name_str;
    let* addr = KB.collect T.Label.addr label in
    let addr_str =
      Option.value_map addr
        ~default:"none"
        ~f:(fun x -> Format.asprintf "%a" Bitvec.pp x)
    in
    Format.printf "-- -- Addr: %s\n" addr_str;
    let* raw_data = data in
    Format.printf "-- -- data: %a\n" KB.Value.pp raw_data;
    let bil_of_data = KB.Value.get Bil.slot raw_data in
    Format.printf "-- -- BIL of data: %s\n" (Bil.to_string bil_of_data);
    let asm_of_data = KB.Value.get Insn.Slot.asm raw_data in
    Format.printf "-- -- ASM of data: %s\n" asm_of_data;
    let opcode_of_data = KB.Value.get Insn.Slot.name raw_data in
    Format.printf "-- -- Opcode of data: %s\n" opcode_of_data;
    let* raw_ctrl = ctrl in
    Format.printf "-- -- ctrl: %a\n" KB.Value.pp raw_ctrl;
    let bil_of_ctrl = KB.Value.get Bil.slot raw_ctrl in
    Format.printf "-- -- BIL of ctrl: %s\n" (Bil.to_string bil_of_ctrl);
    let asm_of_ctrl = KB.Value.get Insn.Slot.asm raw_ctrl in
    Format.printf "-- -- ASM of ctrl: %s\n" asm_of_ctrl;
    let opcode_of_ctrl = KB.Value.get Insn.Slot.name raw_ctrl in
    Format.printf "-- -- Opcode of ctrl: %s\n" opcode_of_ctrl;
    blk label data ctrl

  let set (v : 'a T.var) (value : 'a T.pure) : T.data T.eff =
    Format.printf "SET==========\n";
    let var_name = T.Var.name v in
    let var_sort = T.Var.sort v in
    Format.printf "-- -- Var: %s\n" var_name;
    Format.printf "-- -- Var sort: %a\n" T.Value.Sort.pp var_sort;
    let* raw_value = value in
    let value_sort = T.Value.sort raw_value in
    Format.printf "-- -- Value: %a\n" KB.Value.pp raw_value;
    Format.printf "-- -- Value sort: %a\n" T.Value.Sort.pp value_sort;
    let exp = KB.Value.get Exp.slot raw_value in
    Format.printf "-- -- Value exp: %a\n" Exp.pp exp;
    Format.printf "-- Sem | %s := %a\n" var_name Exp.pp exp;
    set v value

  let var (v : 'a T.var) : 'a T.pure =
    Format.printf "VAR==========\n";
    let var_name = T.Var.name v in
    let var_sort = T.Var.sort v in
    Format.printf "-- -- Var: %s\n" var_name;
    Format.printf "-- -- Var sort: %a\n" T.Value.Sort.pp var_sort;
    Format.printf "-- Sem | Whatever is stored in %s\n" var_name;
    var v

  let int (s : 's T.Bitv.t T.Value.sort) (w : T.word) : 's T.bitv =
    Format.printf "INT==========\n";
    let size = T.Bitv.size s in
    Format.printf "-- -- Bitwidth: %d\n" size;
    Format.printf "-- -- Word: %a\n" Bitvec.pp w;
    Format.printf "-- -- Decimal value: %d\n" (Bitvec.to_int w);
    Format.printf "-- Sem | %a\n" Bitvec.pp w;
    int s w

end 