module Sql = Sqlite3

type sqltype = NONE | NULL | INT | FLOAT | TEXT | BLOB [@deriving string]
type schema = string * (string * string) list
let exec_schema (name, fields) = fun db -> 
  Format.fprintf Format.str_formatter "CREATE TABLE %s ( %a);" name  (Format.pp_print_list 
  ~pp_sep:(fun pp _ -> Format.pp_print_char pp ',') 
  (fun pp (col, coltype) -> 
    Format.fprintf pp "%s %s NOT NULL" col coltype)) 
  fields;
  let schema_sql = Format.flush_str_formatter () in
  Sql.exec db schema_sql

let unop_schema = ("unop" ,["out", "TEXT"; "op", "TEXT"; "a", "TEXT"])
let main _ =
  let schema = "CREATE TABLE unop ( " ^
  "    out TEXT NOT NULL, " ^
  "    op TEXT NOT NULL," ^
  "    a  TEXT NOT NULL" ^
  ");" 
  in
  let insert_sql = "INSERT INTO unop " ^
    "(out, op, a) " ^
    "VALUES (?, ?, ?)"
  in

  (* Construct database and statements *)
  let db = Sql.db_open "t_values.db" in
  (* ignore (Sql.exec db schema); *)
  ignore (exec_schema unop_schema db);
  let insert_stmt = Sql.prepare db insert_sql in


  let unop out op a =
    ignore (Sql.reset insert_stmt);
    ignore (Sql.bind_text insert_stmt 1 out);
    ignore (Sql.bind_text insert_stmt 2 op);
    ignore (Sql.bind_text insert_stmt 3 a);
    ignore (Sql.step insert_stmt)
  in
  unop "r1" "mov" "r0";
    (* Clean up *)
  ignore (Sql.finalize insert_stmt);
  assert (Sql.db_close db);
  ()

let () = main ()