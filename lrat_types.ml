type id = Base of int | Quotient of id * id
      
type pos = int
type lit = int

let base_id i = Base i
  
let merge_ids a b =
  Quotient (b, a)

    
let rec get_base id = match id with
    Base _ -> id
  | Quotient (a,b) -> get_base a

let rec occurs_in_id a b =
  false
    
let rec iter_id f id = match id with
    Base i -> f i
  | Quotient (a,b) -> iter_id f a; iter_id f b

let numerator id = match id with
    Base _ -> failwith "Non quotient id"
  | Quotient (a,b) -> a

let rec is_in id a =
   id = a 
     
type clause = Ptset.t

module IdMap = Map.Make(struct type t = id let compare = compare end)
  
type clause_hist =
  { id : id;
    clause : clause;
    pivot : lit option;
    rup : id list;
    rats : (id list) IdMap.t
  }
           
type line =
    Delete of id list
  | Rat of clause_hist
      
exception Not_a_RAT
  
let get_pivot ch =
  match ch.pivot with
    Some l -> l
  | None -> raise Not_a_RAT

let is_RAT ch =
  match ch.pivot with
    Some _ -> true
  | None -> false
     
let print_clause c =
  Ptset.iter (Printf.printf "%i ") c

open Format

    
let rec pp_id ppf a = match a with
    Base i -> fprintf ppf "%i" i
  | Quotient (a,b) ->
     fprintf ppf "%a_%a_" pp_id a pp_id b
  
let pp_cid ppf i = fprintf ppf "c%a" pp_id i
    
let pp_lit_dk ppf i =
  if i > 0 then
    fprintf ppf "p%d" i
  else
    fprintf ppf "(not p%d)" (-i)


let pp_clause_dk ppf c =
  let nb_par = Ptset.fold (fun lit i ->
    if i > 0 then fprintf ppf "(";
    fprintf ppf "add@ %a@ "
      pp_lit_dk lit;
    i+1) c 0 in
  fprintf ppf "empty";
  for i = 2 to nb_par do
    fprintf ppf ")"
  done

type env_lit =
  | From_clause of id
  | From_pred
  | From_rat of id
  | From_self of id
  | From_subrat of id
      
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
  | From_subrat i -> Format.fprintf ppf "From_subrat %a" pp_id i

let pp_env ppf =
  Env.iter (fun k v -> Format.fprintf ppf "@[<hov2>%i -> %a;@]@ " k pp_env_lit v)
