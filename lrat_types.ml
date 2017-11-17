type id = int * Ptset.t
      
type pos = int
type lit = int

let base_id i = i, Ptset.empty
  
let merge_ids a b =
  let i, ca = a in
  let j, cb = b in
  if i = j && ca = Ptset.empty && Ptset.cardinal cb = 1 then
    Ptset.choose cb, Ptset.singleton i
  else
    j, Ptset.(union cb @@ add i ca)

let occurs_in_id (j,e) (i,s) =
  merge_ids (j,e) (i,s) = (i, s)
  
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
  
let pp_cid ppf i = fprintf ppf "c%a" pp_id i
    
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



type env_lit =
  | From_clause of id
  | From_pred
  | From_rat of id
  | From_self of id
      
module Env = Map.Make
  (struct
    type t = lit
    let compare = compare
   end)

type env = env_lit Env.t

let pp_env_lit ppf = function
  | From_clause i -> Format.fprintf ppf "From_clause %a" pp_cid i
  | From_pred  -> Format.fprintf ppf "From_pred"
  | From_rat i-> Format.fprintf ppf "From_rat %a" pp_cid i
  | From_self i -> Format.fprintf ppf "From_self %a" pp_id i

let pp_env ppf =
  Env.iter (fun k v -> Format.fprintf ppf "@[<hov2>%i -> %a;@]@ " k pp_env_lit v)
