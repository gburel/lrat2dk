open Lrat_types

module PP = Ipl.Proof_steps

let read_cnf f deleted =
  let ic = open_in f in
  let lexbuf = Lexing.from_channel ic in
  let nb_vars, nb_clauses = Dimacs_lexer.first_line lexbuf in
  Ipl.declare_preds Globals.dedukti_out 1 nb_vars;
  try
    while true do
      let c = Dimacs_lexer.line lexbuf in
      let i = c.id in
        Format.(fprintf Globals.dedukti_out  "@[def C%a : clause :=@ %a.@]@."
                  pp_id c.id Lrat_types.pp_clause_dk c.clause);
      if Ptset.mem i deleted then () else
        Lrat_ipl.add_clause i c.clause
    done
  with End_of_file ->
    close_in ic;
    Printf.printf "Read CNF file %s\n" f;
    flush stdout;
    let open Format in
    let open PP in
    begin_proof Globals.dedukti_out nb_clauses


let last_id = ref (base_id (-1))

let process_rat ({id} as ch) =
  let ch,id = if Lrat_ipl.exists_clause id then
      let id = base_id @@ !last_id + 1 in
      { ch with id }, id
    else ch,id in
  Lrat_ipl.define_clauses ch;
  id

let read_lrat f =
  let ic = open_in f in
  let lexbuf = Lexing.from_channel ic in
  begin
    match Lrat_lexer.line lexbuf with
      Delete _ -> () (* first line already processed *)
    | Rat ch ->
       last_id := process_rat ch
  end;
  try
    while true do
      let line = Lrat_lexer.line lexbuf in
      match line with
        Delete l ->  List.iter (Lrat_ipl.remove_all) l
      | Rat ch ->
         last_id := process_rat ch
    done
  with End_of_file ->
    close_in ic;
    PP.end_proof Globals.dedukti_out !last_id;
    Printf.printf "Read LRAT file %s\n" f
  | e ->
     let open Lexing in
     Printf.fprintf stderr "Error in file %s at line %i, character %i\n"
       f
       lexbuf.lex_start_p.pos_lnum
       (lexbuf.lex_start_p.pos_cnum - lexbuf.lex_start_p.pos_bol);
     raise e

let get_deleted f =
  let ic = open_in f in
  let lexbuf = Lexing.from_channel ic in
  let deleted = Deleted_lexer.line lexbuf in
  close_in ic;
  deleted

let _ =
  if Array.length Sys.argv < 3 then
    Printf.fprintf stderr "Usage: %s file.cnf file.lrat\n" Sys.argv.(0)
  else
    let ic = open_in "dedukti_prefix" in
    try
      while true do Format.fprintf Globals.dedukti_out "%s@." (input_line ic)
      done
    with End_of_file ->
      close_in ic;
      let deleted = get_deleted Sys.argv.(2) in
      read_cnf Sys.argv.(1) deleted;
      read_lrat Sys.argv.(2);
