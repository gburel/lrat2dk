{
  open Lrat_types
}
let nat = ['0'-'9']+
let int = '-'?nat

rule idsnl accu = parse
  [' ''\t']+ { idsnl accu lexbuf }
| '0'+[' ''\t']*'\n' { Lexing.new_line lexbuf; accu }
| nat as n { idsnl (int_of_string n::accu) lexbuf }

and rats id as_list clause rup pivot cur_accu rats_accu = parse
  [' ''\t']+ { rats id as_list clause rup pivot cur_accu rats_accu lexbuf }
| '0'+[' ''\t']*'\n' { Lexing.new_line lexbuf;
                       Rat { id; as_list; clause; rup; rats = (pivot, cur_accu)::rats_accu } }
| '-'(nat as n) { rats id as_list clause rup (int_of_string n) [] ((pivot, cur_accu)::rats_accu) lexbuf }
| nat as n { rats id as_list clause rup pivot ((int_of_string n)::cur_accu) rats_accu lexbuf }

and rup id as_list clause accu = parse
  [' ''\t']+ { rup id as_list clause accu lexbuf }
| '0'+[' ''\t']*'\n' { Lexing.new_line lexbuf;
                       Rat { id; as_list; clause;
                             rup = List.rev accu; rats = [] } }
| '-'(nat as n) { rats id as_list clause (List.rev accu) (int_of_string n) [] [] lexbuf }
| nat as n { rup id as_list clause (int_of_string n :: accu) lexbuf }
    
and line_accu id as_list accu = parse
  [' ''\t']+ { line_accu id as_list accu lexbuf }
| '0' { rup id (List.rev as_list) accu [] lexbuf }
| int as s {
  let n = int_of_string s in 
  line_accu id (n::as_list) (Ptset.add (int_of_string s) accu) lexbuf }
    
and line_cont id = parse
  [' ''\t']+ { line_cont id lexbuf }
| 'd' { Delete (idsnl [] lexbuf) }
| '0' { rup id [] Ptset.empty [] lexbuf }
| int as s { let n = int_of_string s in
             line_accu id [n] (Ptset.singleton n) lexbuf }

and line = parse
  [' ''\t']+ { line lexbuf }
| nat as n { line_cont (int_of_string n) lexbuf }
| eof { raise End_of_file }
