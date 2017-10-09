{
  open Lrat_types
}
let nat = ['0'-'9']+
let int = '-'?nat
let space = [' ''\t']
  
rule litsnl as_list clause = parse
  [' ''\t']+ { litsnl as_list clause lexbuf }
| '0'+[' ''\t']*'\n' {
  let id = Lexing.(lexbuf.lex_start_p.pos_lnum) in
  let r = { id; as_list = List.rev as_list; clause; rup = []; rats = [] } in
  Lexing.new_line lexbuf; r }
| int as s {
  let n = int_of_string s in
  litsnl (n::as_list) (Ptset.add n clause) lexbuf }
| eof { raise End_of_file }

and first_line = parse     
  'p'space+"cnf"space+(nat as v)space+(nat as c)space*'\n' {
    int_of_string v, int_of_string c
  }
{
   let line = litsnl [] Ptset.empty     
}      
