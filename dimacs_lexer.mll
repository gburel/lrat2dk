{
  open Lrat_types
}
let nat = ['0'-'9']+
let int = '-'?nat
let space = [' ''\t']
  
rule litsnl clause = parse
  [' ''\t']+ { litsnl clause lexbuf }
| '0'+[' ''\t']*'\n' {
  let id = base_id (Lexing.(lexbuf.lex_start_p.pos_lnum)) in
  let r = { id; clause; pivot = None; rup = []; rats = IdMap.empty } in
  Lexing.new_line lexbuf; r }
| int as s {
  let n = int_of_string s in
  litsnl (Ptset.add n clause) lexbuf }
| eof { raise End_of_file }

and first_line = parse     
  'p'space+"cnf"space+(nat as v)space+(nat as c)space*'\n' {
    int_of_string v, int_of_string c
  }
{
   let line = litsnl Ptset.empty
}      
