type id = int
type pos = int
type lit = int

type clause = Ptset.t

type clause_hist =
  { id : id;
    as_list : lit list;
    clause : clause;
    rup : id list;
    rats : (id * id list) list
  }
           
type line =
    Delete of id list
  | Rat of clause_hist
      
let print_clause c =
  Ptset.iter (Printf.printf "%i ") c

open Format
    
let pp_lit_dk ppf i =
  if i > 0 then
    fprintf ppf "p%d" i
  else
    fprintf ppf "(not p%d)" (-i)

let rec pp_clause_par_dk ppf l =
  match l with
    [] -> fprintf ppf "empty"
  | x :: q -> fprintf ppf "@[(add %a@ %a)@]"
     pp_lit_dk x pp_clause_par_dk q
      
let pp_clause_dk ppf l =
  match l with
    [] -> fprintf ppf "empty"
  | x :: q -> fprintf ppf "@[add %a@ %a@]"
     pp_lit_dk x pp_clause_par_dk q
