let id = ['0'-'9''_']+
let space = [' ''\t''\n']
  
rule filter_decl tbl = parse
| space+"def"space+'c'(id as id)[^'.']*'.' {
  if not @@ Hashtbl.mem tbl id then
    print_string @@ Lexing.lexeme lexbuf;
  filter_decl tbl lexbuf
}
| [^'.']*'.' { print_string @@ Lexing.lexeme lexbuf; filter_decl tbl lexbuf }
| (space* as fin)eof { print_string fin }
