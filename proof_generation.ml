open Lrat_types

module PP = Ipl.Proof_steps

let read_cnf f =
  let ic = open_in f in
  let lexbuf = Lexing.from_channel ic in
  let nb_vars, nb_clauses = Dimacs_lexer.first_line lexbuf in
  for i = 1 to nb_vars do
    Format.fprintf Globals.dedukti_out "p%d : o.@." i
    done;
  try
    while true do
      let c = Dimacs_lexer.line lexbuf in
      Format.(fprintf Globals.dedukti_out  "@[def C%s : clause :=@ %a.@]@."
                c.id Lrat_types.pp_clause_dk c.as_list);
      Hashtbl.add Globals.clause_map c.id c
    done
  with End_of_file ->
    close_in ic;
    let open Format in
    let open PP in
    begin_proof Globals.dedukti_out nb_clauses
    
    
    
let read_lrat f =      
  let ic = open_in f in
  let lexbuf = Lexing.from_channel ic in
  let last_id = ref "bad_clause" in
  try
    while true do
      let line = Lrat_lexer.line lexbuf in
      match line with
        Delete l -> List.iter (Hashtbl.remove Globals.clause_map) l
      | Rat ( {id; clause; rup } as ch) -> Hashtbl.add Globals.clause_map id ch;
        let iplterm = Lrat_ipl.define_clause ch in
        last_id := id;
        Format.fprintf Globals.dedukti_out
          "%a@." PP.pp_clause_term iplterm
    done
  with End_of_file ->
    close_in ic;
    PP.end_proof Globals.dedukti_out !last_id;
    Printf.printf "Read LRAT file %s\n" f
  | Failure _ as e ->
     let open Lexing in
     Printf.fprintf stderr "Parsing error in file %s at line %i, character %i\n"
       lexbuf.lex_start_p.pos_fname
       lexbuf.lex_start_p.pos_lnum
       (lexbuf.lex_start_p.pos_cnum - lexbuf.lex_start_p.pos_bol);
     raise e
  
  
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
      read_cnf Sys.argv.(1);
      read_lrat Sys.argv.(2);
      

     
