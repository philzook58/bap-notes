let pp_mlcfg ppf proj = ()

let () = Extension.declare @@ fun _ctxt ->
  let pp_mlcfg =  Regular.Std.Data.Write.create ~pp:(pp_mlcfg) () in
  Project.add_writer  ~ver:"1" "mlcfg"
    ~desc:"dumps a why3 mlcfg" pp_mlcfg;
  Ok ()