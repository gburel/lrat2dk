{
  let tbl = Hashtbl.create 503
}
let id = ['0'-'9''_']+
let space = [' ''\t''\n']
  
rule read_decl = parse
  space+ { read_decl lexbuf }
| "def"space+'c'(id as id) {
  Hashtbl.add tbl id ();
  remove_used lexbuf }
| "def"space+"proof" {
  remove_used lexbuf }
| _ { other_decl lexbuf }      
| eof { () }

and remove_used = parse     
  space+ { remove_used lexbuf }
| 'c'(id as id) { Hashtbl.remove tbl id; remove_used lexbuf }
| [^' ''\t''\n''.']+ { remove_used lexbuf }
| '.' { read_decl lexbuf }

and other_decl = parse
  [^'.']*'.' { read_decl lexbuf }
{
   let analyse lexbuf = Hashtbl.clear tbl; read_decl lexbuf; tbl
}      
