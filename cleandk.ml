open Analyse_lexer

let _ =
  if Array.length Sys.argv < 2 then
    Printf.fprintf stderr "Usage: %s file.dk\n" Sys.argv.(0)
  else
    let ic = open_in Sys.argv.(1) in
    let lexbuf = Lexing.from_channel ic in
    let tbl = analyse lexbuf in
    close_in ic;
    if Hashtbl.length tbl = 0 then
      begin
        Printf.fprintf stderr "No need to clean file %s\n" Sys.argv.(1);
        exit 1
      end
    else
      let ic = open_in Sys.argv.(1) in
      let lexbuf = Lexing.from_channel ic in
      Filter_lexer.filter_decl tbl lexbuf;
      close_in ic
