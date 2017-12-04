{
  open Lrat_types

  let base s = base_id (int_of_string s)
}
let nat = ['0'-'9']+
let int = '-'?nat

rule idsnl accu = parse
  [' ''\t']+ { idsnl accu lexbuf }
| '0'+[' ''\t']*'\n' { Lexing.new_line lexbuf; accu }
| nat as n { idsnl (base n::accu) lexbuf }

and rats id clause pivot rup otherid cur_accu rats_accu = parse
  [' ''\t']+ { rats id clause pivot rup otherid cur_accu rats_accu lexbuf }
| '0'+[' ''\t']*'\n' { Lexing.new_line lexbuf;
                       Rat { id; clause; pivot = Some pivot; rup; rats = IdMap.add otherid (List.rev cur_accu) rats_accu } }
| '-'(nat as n) { rats id clause pivot rup (base n) [] (IdMap.add otherid (List.rev cur_accu) rats_accu) lexbuf }
| nat as n { rats id clause pivot rup otherid (base n::cur_accu) rats_accu lexbuf }

and rup id clause pivot accu = parse
  [' ''\t']+ { rup id clause pivot accu lexbuf }
| '0'+[' ''\t']*'\n' { Lexing.new_line lexbuf;
                       Rat { id; clause; pivot = None;
                             rup = List.rev accu; rats = IdMap.empty } }
| '-'(nat as n) { rats id clause pivot (List.rev accu) (base n) [] IdMap.empty lexbuf }
| nat as n { rup id clause pivot (base n :: accu) lexbuf }
    
and line_accu id accu pivot = parse
  [' ''\t']+ { line_accu id accu pivot lexbuf }
| '0' { rup id accu pivot [] lexbuf }
| int as s {
  let n = int_of_string s in 
  line_accu id (Ptset.add n accu) pivot lexbuf }
    
and line_cont id = parse
  [' ''\t']+ { line_cont id lexbuf }
| 'd' { Delete (idsnl [] lexbuf) }
| '0' { rup id Ptset.empty 0 [] lexbuf }
| int as s { let n = int_of_string s in
             line_accu id (Ptset.singleton n) n lexbuf }

and line = parse
  [' ''\t']+ { line lexbuf }
| nat as n { line_cont (base n) lexbuf }
| eof { raise End_of_file }
