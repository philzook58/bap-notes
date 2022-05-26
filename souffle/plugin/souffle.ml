open Bap_core_theory
open Core_kernel[@@warning "-D"]
open Regular.Std
open Graphlib.Std
open Bap.Std
open Format
open Bap_main
let section_name memory start =
  Memmap.lookup memory start |>
  Seq.find_map ~f:(fun (mem,tag) ->
      match Value.get Image.section tag with
      | Some name when Addr.equal (Memory.min_addr mem) start ->
        Some name
      | _ -> None) |>
  function Some name -> name
         | None -> Format.asprintf ".section@%a" Addr.pp start

let sort_fns fns =
  let fns = Array.of_list_rev fns in
  Array.sort fns ~compare:(fun (_,b1,_) (_,b2,_) ->
      Block.compare b1 b2);
  Seq.of_array fns
let pp_addr ppf a =
  Addr.pp_generic ~prefix:`none ~case:`lower ppf a

let sorted_blocks nodes =
  let init = Set.empty (module Block) in
  Seq.fold nodes ~init ~f:Set.add |>
  Set.to_sequence

let add_dollar s =
  let regex = Str.regexp {|[A-Z][A-Za-z]*(|} in
  Str.global_replace regex {|$\0|} s

let print_disasm pp_insn patterns ppf proj =
  let memory = Project.memory proj in
  let syms = Project.symbols proj in
  (* pp_open_tbox ppf ();
  setup_tabs ppf; *)
  Memmap.filter_map memory ~f:(Value.get Image.code_region) |>
  Memmap.to_sequence |> Seq.iter ~f:(fun (mem,()) ->
      let sec = section_name memory (Memory.min_addr mem) in
      Symtab.intersecting syms mem |>
      (* List.filter ~f:(fun (_,entry,_) ->
          matches patterns proj (Some (Block.addr entry)))  |> *) function
      | [] -> ()
      | fns ->
        (* fprintf ppf "@\nDisassembly of section %s@\n" sec; *)
        Seq.iter (sort_fns fns) ~f:(fun (name,entry,cfg) ->
            (* fprintf ppf "@\n%a: <%s>@\n" pp_addr (Block.addr entry) name; *)
            sorted_blocks (Graphs.Cfg.nodes cfg) |> Seq.iter ~f:(fun blk ->
                let mem = Block.memory blk in
                (* fprintf ppf "%a:@\n" pp_addr (Memory.min_addr mem); *)
                Block.insns blk |> List.iter ~f:(pp_insn syms blk ppf))));
  pp_close_tbox ppf ()

  (* https://github.com/BinaryAnalysisPlatform/bap/blob/253afc171bbfd0fe1b34f6442795dbf4b1798348/lib/bap_types/bap_bil_adt.ml *)
let pp_bil fmt _ _ ppf (mem,insn) =
  let pp_bil ppf = Bil.Io.print ~fmt ppf in
  let addr = Memory.min_addr mem in
  (* fprintf str_formatter "%a" pp_bil (Insn.bil insn);
  let adt = flush_str_formatter () |> add_dollar in *)
  fprintf ppf "0x%a,\"%s\",%a@\n" pp_addr addr (Insn.asm insn)
    pp_bil (Insn.bil insn)


let pp_souffle ppf proj = ()
(*https://github.com/BinaryAnalysisPlatform/bap/blob/master/plugins/print/print_main.ml*)
let () = Extension.declare @@ fun _ctxt ->
  Ppsouffle.add_souffle_writers ();
  (* let pp_mlcfg =  Data.Write.create ~pp:(pp_souffle) () in
  Project.add_writer  ~ver:"1" "souffle"
  ~desc:"dumps a souffle file" pp_mlcfg; *)
  let patterns = [] in
  let ver = "1" in
  let pp_disasm_bil =
    Data.Write.create ~pp:(print_disasm (pp_bil "souffle") patterns) () in
    Project.add_writer ~ver "souffle"
    ~desc:"print BIL instructions" pp_disasm_bil;
  Ok ()