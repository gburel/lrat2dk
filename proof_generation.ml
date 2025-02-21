open Lrat_types

module PP = Ipl.Proof_steps

let read_cnf f deleted dedukti_out =
  let ic = open_in f in
  let lexbuf = Lexing.from_channel ic in
  let nb_vars, nb_clauses = Dimacs_lexer.first_line lexbuf in
  Ipl.declare_preds dedukti_out 1 nb_vars;
  for i = 1 to nb_vars do Lrat_ipl.create_lit i; Lrat_ipl.create_lit (-i) done;
  try
    while true do
      let c = Dimacs_lexer.line lexbuf in
      let i = c.id in
        Format.(fprintf dedukti_out  "@[def C%a : clause :=@ %a.@]@."
                  pp_id c.id (Lrat_types.pp_clause_dk empty_subst) c.clause);
      if Ptset.mem i deleted then () else
        Lrat_ipl.add_clause i c.clause
    done
  with End_of_file ->
    close_in ic;
    Printf.printf "Read CNF file %s\n" f;
    flush stdout;
    let open Format in
    let open PP in
    begin_proof dedukti_out nb_clauses


let last_id = ref (base_id (-1))

let process_rat dedukti_out s ({id} as ch) =
  let ch,id = if Lrat_ipl.exists_clause id then
      let id = base_id @@ !last_id + 1 in
      { ch with id }, id
    else ch,id in
  let s = Lrat_ipl.define_clauses dedukti_out s ch in
  id, s

let read_lrat f dedukti_out =
  let subst = ref Lrat_types.empty_subst in
  let ic = open_in f in
  let lexbuf = Lexing.from_channel ic in
  begin
    match Lrat_lexer.line lexbuf with
      Delete _ -> () (* first line already processed *)
    | Rat ch ->
       let i, s = process_rat dedukti_out !subst ch in
       last_id := i;
       subst := s
  end;
  try
    while true do
      let line = Lrat_lexer.line lexbuf in
      match line with
        Delete l ->  List.iter (Lrat_ipl.remove_all) l
      | Rat ch ->
       let i, s = process_rat dedukti_out !subst ch in
       last_id := i;
       subst := s
    done
  with End_of_file ->
    close_in ic;
    PP.end_proof !subst dedukti_out !last_id;
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
  if Array.length Sys.argv < 2 then
    Printf.fprintf stderr "Usage: %s prefix\n\tprefix.cnf contains the problem\n\tprefix.lrat contains the proof\n\tThe dedukti term is written in prefix.dk\n" Sys.argv.(0)
  else
    let cnf_file = Sys.argv.(1) ^ ".cnf" in
    let lrat_file = Sys.argv.(1) ^ ".lrat" in
    let dk_file = Sys.argv.(1) ^ ".dk" in
    let ic = open_in "dedukti_prefix" in
    let dedukti_out =
      let oc = open_out dk_file in
      Format.formatter_of_out_channel oc
    in
    try
      while true do Format.fprintf dedukti_out "%s@." (input_line ic)
      done
    with End_of_file ->
      close_in ic;
      let deleted = get_deleted lrat_file in
      read_cnf cnf_file deleted dedukti_out;
      read_lrat lrat_file dedukti_out
