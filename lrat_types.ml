(* type of identifiers for clauses *)
type id = int

let base_id i = i

(* type of literals, as in DIMACS format *)
type lit = int

(* type for clauses *)
type clause = Ptset.t

module IdMap = Map.Make(struct type t = id let compare = compare end)

(* clause with history *)
type clause_hist =
  { id : id; (* identifier *)
    clause : clause; (* set of literals *)
    pivot : lit option;  (* literal used as pivot in a real RAT clause *)
    rup : id list; (* list of clauses with which UCP has to be done *)
    rats : (id list) IdMap.t (* maps each clause containing the negated pivot
                                to the list of clause identifiers used in UCP *)
  }

(* a line of LRAT format *)
type line =
    Delete of id list
  | Rat of clause_hist

(* exception raised if the clause is not properly RAT, i.e. is RUP *)
exception Not_a_RAT

let get_pivot ch =
  match ch.pivot with
    Some l -> l
  | None -> raise Not_a_RAT

let is_RAT ch =
  match ch.pivot with
    Some _ -> true
  | None -> false

(* print the literals of the clause *)
let print_clause c =
  Ptset.iter (Printf.printf "%i ") c

(* an extended literal is either a literal of the input,
   or a literal created by extended resolution *)
type extended_lit = Real of lit | Extended of int

let new_extended_lit =
  let counter = ref 0 in
  fun () -> incr counter; Extended !counter


module ELMap = Map.Make(struct type t = extended_lit let compare = compare end)

(* renaming of literals *)
type el_subst = extended_lit ELMap.t

(* an extended clause is either a clause from the LRAT file
   or a clause added by the translation to extended resolution *)
type extended_id = Orig of id | New of int

let new_extended_id =
  let counter = ref 0 in
  fun () -> incr counter; New !counter

module ECMap = Map.Make(struct type t = extended_id let compare = compare end)
(* renaming of clauses *)
type ec_subst = extended_id ECMap.t

(* renaming environment *)
type subst = { el : el_subst; ec : ec_subst }

(* empty renaming *)
let empty_subst = { el = ELMap.empty; ec = ECMap.empty }

(* recursively find by which literal the input literal has been renamed *)
let find_extended_lit s lit =
  let rec find_aux el =
    try
      let el' = ELMap.find el s.el in
      find_aux el'
    with Not_found -> el
  in find_aux (Real lit)

(* negate the given literal *)
let neg_el = function
  | Real i -> Real (-i)
  | Extended i -> Extended (-i)

(* test if the literal is positive *)
let is_pos = function
  | Real i | Extended i -> i > 0

(* add a new literal renaming to the environment subst *)
let add_extended_lit subst old neu =
  let s = ELMap.add old neu subst.el in
  { subst with el = ELMap.add (neg_el old) (neg_el neu) s }


(* recursively find by which clause the input clause has been renamed *)
let find_extended_id s c =
  let rec find_aux ec =
    try
      let ec' = ECMap.find ec s.ec in
      find_aux ec'
    with Not_found -> ec
  in find_aux (Orig c)

(* add a new clause renaming to the environment subst *)
let add_extended_id subst old neu =
  { subst with ec = ECMap.add old neu subst.ec }


open Format

(* pretty print LRAT clause identifier *)
let rec pp_id ppf a = fprintf ppf "%i" a

(* pretty print extended clause identifier *)
let pp_eid ppf ec =
  match ec with
    Orig id ->  fprintf ppf "c%a" pp_id id
  | New i -> fprintf ppf "n%i" i

(* pretty print extended clause identifier after renaming *)
let pp_cid s ppf i =
  let ec = find_extended_id s i in
  pp_eid ppf ec

(* pretty print extended literal *)
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

(* pretty print extended literal after renaming *)
let pp_lit_dk s ppf i =
  let el = find_extended_lit s i in
  pp_el_dk ppf el

(* pretty print clause in the given renaming environment *)
let pp_clause_dk s ppf c =
  let nb_par = Ptset.fold (fun lit i ->
    if i > 0 then fprintf ppf "(";
    fprintf ppf "add@ %a@ "
      (pp_lit_dk s) lit;
    i+1) c 0 in
  fprintf ppf "empty";
  for i = 2 to nb_par do
    fprintf ppf ")"
  done

(* pretty print negated clause in the given renaming environment *)
let pp_neg_clause_dk s ppf c =
  let nb_par = Ptset.fold (fun lit i ->
    if i > 0 then fprintf ppf "(";
    fprintf ppf "add@ %a@ "
      (pp_lit_dk s) (-lit);
    i+1) c 0 in
  fprintf ppf "empty";
  for i = 2 to nb_par do
    fprintf ppf ")"
  done

(* origin of a literal in a model *)
type env_lit =
  | From_clause of id (* UCP of clause id *)
  | From_pred (* literal being constructed *)
  | From_self of id (* RUP clause id *)

module Env = Map.Make
  (struct
    type t = lit
    let compare = compare
   end)

(* map from literal to their origin *)
type env = env_lit Env.t

let pp_env_lit ppf = function
  | From_clause i -> Format.fprintf ppf "From_clause %a" (pp_cid empty_subst) i
  | From_pred  -> Format.fprintf ppf "From_pred"
  | From_self i -> Format.fprintf ppf "From_self %a" pp_id i

let pp_env ppf =
  Env.iter (fun k v -> Format.fprintf ppf "@[<hov2>%i -> %a;@]@ " k pp_env_lit v)
