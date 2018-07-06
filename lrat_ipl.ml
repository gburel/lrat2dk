open Lrat_types
open Ipl

module IdSet = Set.Make(struct type t = id let compare = compare end)

let push_decl ct =
  Format.(fprintf Globals.dedukti_out "%a@." Proof_steps.pp_clause_term ct)

let declare_new_pred ch =
  let max_lit = Ptset.fold (fun l m -> max (abs l) m) ch.clause 0 in
  if max_lit > !Globals.max_pred then
    declare_preds Globals.dedukti_out (!Globals.max_pred + 1) max_lit;
  push_decl @@ Declare_clause(ch.id, ch.clause)
    
exception Tautology of lit
  
let rec find_tauto clause =
  try
    let _ = Ptset.fold (fun i model ->
      if Ptset.mem (-i) model then raise (Tautology i)
      else Ptset.add i model) clause Ptset.empty
    in raise Not_found
  with Tautology i ->
    i

let create_tauto id clause =
  let i = find_tauto clause in
  let ch = { id; clause; pivot = None; rup = []; rats = IdMap.empty } in
  push_decl (Let_clause(id, ch.clause, Tauto i));
  ch
             


(* Map id -> clause
   implemented as an Hashtbl *)
let clausemap : (id, clause) Hashtbl.t = Hashtbl.create 251

(* Map lit -> id set
   set of clauses in which lit appears *)
let litmap : (lit, Ptset.t) Hashtbl.t = Hashtbl.create 251
  
  
let find_clause id = Hashtbl.find clausemap id  

let find_lit lit = Hashtbl.find litmap lit
  
let add_lit id lit =
  try
    let s = Hashtbl.find litmap lit in
    Hashtbl.replace litmap lit (Ptset.add id s)
  with Not_found -> Hashtbl.add litmap lit (Ptset.singleton id)
  
let add_clause id c =
  Ptset.iter (add_lit id) c;
  Hashtbl.add clausemap id c

let exists_clause id = Hashtbl.mem clausemap id

let remove_lit id lit =
  let s = Hashtbl.find litmap lit in
  Hashtbl.replace litmap lit (Ptset.remove id s)
  
let remove_all id = (* TODO: check if must remove something else *)
  let c = Hashtbl.find clausemap id in
  Ptset.iter (remove_lit id) c;
  Hashtbl.remove clausemap id
  
let array_of_ptset_map f c =
  let s = Ptset.choose c in
  let a = Array.make (Ptset.cardinal c) (f s) in
  let i = Ptset.fold (fun s i -> Array.unsafe_set a i (f s); i+1)
    c 0 in
  assert (i = Ptset.cardinal c);
  a

exception Not_RUP
        
let rec arg_from_env e cid i =
  try
    match Env.find i e with
      From_clause _ | From_self _ -> Lit i
    | From_pred -> Pred i
  with
    Not_found ->
      let open Format in
      fprintf err_formatter "Literal %i not found in current environment:\n@[<v>" i;
      pp_env err_formatter e;
      fprintf err_formatter "@]@.";
      failwith "Not found"
        
and make_core e id c =
  Core (id,
        array_of_ptset_map (arg_from_env e id) c)

let unit_propagation =
  Ptset.fold Ptset.remove
    

    
    
    
let rec rup e invmodel = function
  | [] -> raise Not_RUP
  | i::q ->
     let ci = find_clause i in
     let propagated = unit_propagation invmodel ci in
     (* unit propagation should falsify all but at most one literal *)
     assert (Ptset.cardinal propagated <= 1);
     match
       try
         (* unit propagation leads to a new unit *)
         let new_lit = Ptset.choose propagated in
         Some new_lit
       with Not_found -> None (* unit propagation leads to a contradiction *)
     with
       Some new_lit -> 
         let new_invmodel = Ptset.add (-new_lit) invmodel in
         let new_e_pred = Env.add new_lit From_pred e in
         let new_e_lit = Env.add (-new_lit) (From_clause i) e in
         Let_o (-new_lit, make_core new_e_pred i ci,
           rup new_e_lit new_invmodel q)
     | None ->
          Qed (make_core e i ci)
      
let prepare_rup c =
  try
      let invmodel = c.clause in
      let e = Ptset.fold (fun i e ->
        if Env.mem (-i) e then raise (Tautology i)
               else Env.add i (From_self c.id) e)
        c.clause Env.empty in
      rup e invmodel c.rup
    with
      Tautology i -> Tauto i
      

let push ch =
  Format.(fprintf err_formatter "Trying to push %a@." pp_id ch.id)[@noopt];
  push_decl @@ Let_clause(ch.id, ch.clause, prepare_rup ch);
  Format.(fprintf err_formatter "Pushed %a@." pp_id ch.id)[@noopt];
  add_clause ch.id ch.clause

let extends_rat ch =
  let p = get_pivot ch in
  let r = Ptset.remove p ch.clause in
(* Define a new variable replacing p *)
  let el = new_extended_lit () in
  push_decl @@ Extended_lit_def (el, p, r);
(* Prove clause deriving from this definition *)
  (* el | r *)
  let eid = new_extended_id () in
  push_decl @@ Implied_clause (eid, el, r);
  (* el | ~p *)
  let eid' = new_extended_id () in
  push_decl @@ Implied_clause (eid', el, Ptset.singleton (- p));
  (* ~el | p | ~ci *)
  Ptset.iter (fun i ->
    let eid' = new_extended_id () in
    push_decl @@
      Implied_clause (eid', op_el el, Ptset.add p (Ptset.singleton (-i))))
    r;
(* Prove new clauses from the existing ones *)
  let clauses_with_p = find_lit p in
  Ptset.iter (fun id ->
    let clause = find_clause id in
    let eid' = new_extended_id () in
    push_decl @@
      Subst_clause (eid', p, el, clause);
    add_extended_id (find_extended_id id) eid'
  ) clauses_with_p;
  IdMap.iter (fun ci rupi ->
    let clause = find_clause ci in
    let eid' = new_extended_id () in
    push_decl @@
      Subst_clause (eid', -p, op_el el, clause);
    add_extended_id (find_extended_id ci) eid')
    ch.rats;
  add_extended_id (find_extended_id ch.id) eid;
  add_extended_lit (find_extended_lit p) el;
  add_clause ch.id ch.clause
    
let define_clauses ch =
  Format.(fprintf err_formatter "Beginning clause %a@."
            pp_id ch.id)[@noopt];
  if not @@ is_RAT ch then
    push ch
  else
    extends_rat ch
