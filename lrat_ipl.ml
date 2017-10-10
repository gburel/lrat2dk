open Lrat_types
open Ipl

type env_lit =
  | From_clause of id
  | From_pred
  | From_rat of id
      
module Env = Map.Make
  (struct
    type t = int
    let compare = compare
   end)

type env = env_lit Env.t

let pp_env_lit ppf = function
  | From_clause i -> Format.fprintf ppf "From_clause %a" pp_cid i
  | From_pred  -> Format.fprintf ppf "From_pred"
  | From_rat i-> Format.fprintf ppf "From_rat %a" pp_cid i

let pp_env ppf =
  Env.iter (fun k v -> Format.fprintf ppf "@[%i -> %a@]@ " k pp_env_lit v)

  
let array_of_list_map f = function
    [] -> [||]
  | hd::tl as l ->
      let a = Array.make (List.length l) (f hd) in
      let rec fill i = function
          [] -> a
        | hd::tl -> Array.unsafe_set a i (f hd); fill (i+1) tl in
      fill 1 tl

let arg_from_env e i =
  try
    match Env.find i e with
      From_clause c -> Lit i
    | From_pred -> Pred i
    | From_rat _ -> failwith "lit from rat: not implemented"
  with
    Not_found as ex ->
      let open Format in
      fprintf err_formatter "Literal %i not found in current environment:\n@[<v>" i;
      pp_env err_formatter e;
      fprintf err_formatter "@]";
      raise ex
    
        
let make_core e ch =
  Core (ch.id,
        array_of_list_map (arg_from_env e) ch.as_list)

let unit_propagation c invmodel =
  List.fold_left (fun cr i -> Ptset.remove i cr)
    c invmodel
    
let rec rup e invmodel = function
  | [] -> failwith "No RUP"
  | [i] ->
     (* unit propagation should falsify all literals *)
     let ci = Hashtbl.find Globals.clause_map i in
     assert (
       let propagated = unit_propagation ci.clause invmodel in
       propagated = Ptset.empty );
     Qed (make_core e ci)
  | i::q ->     
     let ci = Hashtbl.find Globals.clause_map i in
     let propagated = unit_propagation ci.clause invmodel in
     (* unit propagation should falsify all but one literal *)
     assert (Ptset.cardinal propagated = 1);
     let new_lit = Ptset.choose propagated in
     let new_invmodel = (-new_lit)::invmodel in
     let new_e_pred = Env.add new_lit From_pred e in
     let new_e_lit = Env.add (-new_lit) (From_clause i) e in
     Let_o (-new_lit, make_core new_e_pred ci,
            rup new_e_lit new_invmodel q)

let define_clause ch =
  match ch.rats with
    _::_ -> failwith "RAT not implemented yet"
  | [] ->
     let invmodel = ch.as_list in
     let e = List.fold_left (fun e i -> Env.add i (From_clause ch.id) e)
       Env.empty ch.as_list in
     Let_clause(ch.id, ch.as_list,
                rup e invmodel ch.rup)
