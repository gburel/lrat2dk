let nat = ['0'-'9']+
let int = '-'?nat

rule idptset accu = parse
  [' ''\t']+ { idptset accu lexbuf }
| '0'+[' ''\t']*'\n' { Lexing.new_line lexbuf; accu }
| nat as n { idptset (Ptset.add (int_of_string n) accu) lexbuf }

and line_cont = parse
  [' ''\t']+ { line_cont lexbuf }
| 'd' { idptset Ptset.empty lexbuf }
| int { Ptset.empty }

and line = parse
  [' ''\t']+ { line lexbuf }
| nat as n { line_cont lexbuf }
| eof { raise End_of_file }
