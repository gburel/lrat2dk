open Lrat_types
open Ipl

module IdSet = Set.Make(struct type t = id let compare = compare end)

let push_decl s ct =
  Format.(fprintf Globals.dedukti_out "%a@." (Proof_steps.pp_clause_term s) ct)

let declare_new_pred s ch =
  let max_lit = Ptset.fold (fun l m -> max (abs l) m) ch.clause 0 in
  if max_lit > !Globals.max_pred then
    declare_preds Globals.dedukti_out (!Globals.max_pred + 1) max_lit;
  push_decl s @@ Declare_clause(find_extended_id s ch.id, ch.clause)

exception Tautology of lit



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

let rec arg_from_env s e cid i =
  try
    match Env.find i e with
      From_clause _ | From_self _ -> Lit (find_extended_lit s i)
    | From_pred -> Pred (find_extended_lit s i)
  with
    Not_found ->
      let open Format in
      fprintf err_formatter "Literal %i not found in current environment:\n@[<v>" i;
      pp_env err_formatter e;
      fprintf err_formatter "@]@.";
      failwith "Not found"

and make_core s e id c =
  Core (find_extended_id s id,
        array_of_ptset_map (arg_from_env s e id) c)

let unit_propagation =
  Ptset.fold Ptset.remove





let rec rup s e invmodel = function
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
         Let_o (neg_el (find_extended_lit s new_lit),
                make_core s new_e_pred i ci,
           rup s new_e_lit new_invmodel q)
     | None ->
          Qed (make_core s e i ci)

let prepare_rup s c =
  try
      let invmodel = c.clause in
      let e = Ptset.fold (fun i e ->
        if Env.mem (-i) e then raise (Tautology i)
               else Env.add i (From_self c.id) e)
        c.clause Env.empty in
      rup s e invmodel c.rup
    with
      Tautology i -> Tauto (find_extended_lit s i)


let push s ch =
  Format.(fprintf err_formatter "Trying to push %a@." pp_id ch.id)[@noopt];
  push_decl s
  @@ Let_clause(find_extended_id s ch.id, ch.clause, prepare_rup s ch);
  Format.(fprintf err_formatter "Pushed %a@." pp_id ch.id)[@noopt];
  add_clause ch.id ch.clause

let extends_rat s ch =
  let p = get_pivot ch in
  let r = Ptset.remove p ch.clause in
(* Define a new variable replacing p *)
  let el = new_extended_lit () in
  let new_s = add_extended_lit s (find_extended_lit s p) el in
  push_decl s @@ Extended_lit_def (el, p, r);
(* Prove clause deriving from this definition *)
  (* el | r *)
  let eid = new_extended_id () in
  push_decl new_s @@ Let_clause (eid, ch.clause, Extended(el, r));
(* not needed, can do direct proofs
  (* el | ~p *)
  let eid' = new_extended_id () in
  push_decl s @@ Implied_clause (eid', el, Ptset.singleton (- p));
  (* ~el | p | ~ci *)
  Ptset.iter (fun i ->
    let eid' = new_extended_id () in
    push_decl s @@
      Implied_clause (eid', neg_el el, Ptset.add p (Ptset.singleton (-i))))
    r;
*)
  (* Prove new clauses from the existing ones *)
  let clauses_with_p = find_lit p in
  let s' = Ptset.fold (fun id subst ->
    let clause = find_clause id in
    let eid' = new_extended_id () in
    push_decl subst @@
      Let_clause (eid', clause,
                  Let_o (find_extended_lit s p, Proj(el, find_extended_lit s p),
                  Qed (Core (find_extended_id s id, array_of_ptset_map (fun i ->
                    Lit (find_extended_lit s i)) clause)))
      );
    add_extended_id subst (find_extended_id subst id) eid'
  ) clauses_with_p new_s in
  let s =
    IdMap.fold  (fun ci rupi subst ->
      let clause = find_clause ci in
      let fake_clause_hist = { clause = Ptset.union r @@ Ptset.remove (-p) clause;
                               id = -ci;
                               pivot = None;
                               rup = ci :: ch.rup @ rupi;
                               rats = IdMap.empty; } in
      let eid' = new_extended_id () in
      let new_subst = add_extended_id subst (find_extended_id subst ci) eid' in
      let pt_remainder = prepare_rup s fake_clause_hist in
      push_decl new_subst @@
        Let_clause (eid', clause,
                    Let_o (find_extended_lit s p,
                           Core (find_extended_id s ci,
                                 array_of_ptset_map (fun i ->
                                   if i = -p then Pred (find_extended_lit s i)
                                   else Lit (find_extended_lit s i)
                                 ) clause),
                    Let_extended (neg_el el, find_extended_lit s p, r, pt_remainder
                    )));
      new_subst
    )
      ch.rats s' in
  let s = add_extended_id s (find_extended_id s ch.id) eid in
  add_clause ch.id ch.clause; s

let define_clauses s ch =
  Format.(fprintf err_formatter "Beginning clause %a@."
            pp_id ch.id)[@noopt];
  if not @@ is_RAT ch then
    (push s ch; s)
  else
    extends_rat s ch
