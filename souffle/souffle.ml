let pp_souffle ppf proj = ()

let () = Extension.declare @@ fun _ctxt ->
  let pp_mlcfg =  Regular.Std.Data.Write.create ~pp:(pp_souffle) () in
  Project.add_writer  ~ver:"1" "souffle"
    ~desc:"dumps a souffle file" pp_mlcfg;
  Ok ()