type id = int

let base_id i = i
  
type lit = int

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

type extended_lit = Real of lit | Extended of int

let new_extended_lit =
  let counter = ref 0 in
  fun () -> incr counter; Extended !counter

    
let el_table = Hashtbl.create 251

let find_extended_lit lit =
  let rec find_aux el =
    try
      let el' = Hashtbl.find el_table el in
      find_aux el'
    with Not_found -> el
  in find_aux (Real lit)

let op_el = function
  | Real i -> Real (-i)
  | Extended i -> Extended (-i)

let is_pos = function
  | Real i | Extended i -> i > 0
     
let add_extended_lit old neu =
  Hashtbl.add el_table old neu;
  Hashtbl.add el_table (op_el old) (op_el neu)
  

type extended_clause = Orig of id | New of int

let new_extended_id =
  let counter = ref 0 in
  fun () -> incr counter; New !counter

    
let ec_table = Hashtbl.create 251

let find_extended_id c =
  let rec find_aux ec =
    try
      let ec' = Hashtbl.find ec_table ec in
      find_aux ec'
    with Not_found -> ec
  in find_aux (Orig c)

let add_extended_id old neu =
  Hashtbl.add ec_table old neu


open Format

    
let rec pp_id ppf a = fprintf ppf "%i" a

let pp_eid ppf ec = 
  match ec with
    Orig id ->  fprintf ppf "c%a" pp_id id
  | New i -> fprintf ppf "n%i" i
  
let pp_cid ppf i =
  let ec = find_extended_id i in
  pp_eid ppf ec

let pp_el_dk ppf el =
  let p, i =
    match el with
    | Real i -> "p", i
    | Extended i -> "e", i
  in
  if i > 0 then
    fprintf ppf "%s%d" p i
  else
    fprintf ppf "(not %s%d)" p (-i)
  
  
let pp_lit_dk ppf i =
  let el = find_extended_lit i in
  pp_el_dk ppf el

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
  | From_self i -> Format.fprintf ppf "From_self %a" pp_id i

let pp_env ppf =
  Env.iter (fun k v -> Format.fprintf ppf "@[<hov2>%i -> %a;@]@ " k pp_env_lit v)
