type id = int * Ptset.t
      
type pos = int
type lit = int

let base_id i = i, Ptset.empty
  
let merge_ids a b =
  let i, ca = a in
  let j, cb = b in
  j, Ptset.(union cb @@ add i ca)

let occurs_in_id (j,e) (i,s) =
  let open Ptset in
  not @@ is_empty (inter (add j e) (add i s))
    
type clause = Ptset.t

module IdMap = Map.Make(struct type t = id let compare = compare end)
  
type clause_hist =
  { id : id;
    as_list : lit list;
    clause : clause;
    rup : id list;
    rats : (id list) IdMap.t
  }
           
type line =
    Delete of id list
  | Rat of clause_hist
      
let print_clause c =
  Ptset.iter (Printf.printf "%i ") c

open Format

    
let rec pp_id ppf (i, c) =
  fprintf ppf "%i" i;
  if not @@ Ptset.is_empty c then fprintf ppf "_";
  Ptset.iter (fprintf ppf "_%i") c
  
    
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
