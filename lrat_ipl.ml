open Lrat_types
open Ipl

module IdSet = Set.Make(struct type t = id let compare = compare end)

let potential_merge : (lit, IdSet.t) Hashtbl.t = Hashtbl.create 255
  

module type ClauseMap =
sig
  val add : clause_hist -> unit
  val replace : clause_hist -> unit
  val find : id -> clause_hist
  val iter_all : id -> (clause_hist -> unit) -> unit
  val potential_merges : lit -> IdSet.t
  val remove_all : id -> unit
  val exists : id -> bool
  val not_rat : id -> bool
end

module CM : ClauseMap =
struct
  
  let global : (int, (Ptset.t, clause_hist) Hashtbl.t) Hashtbl.t =
    Hashtbl.create 255
  let potential_merge : (lit, IdSet.t) Hashtbl.t = Hashtbl.create 255
  let reverse : (int, (Ptset.t)) Hashtbl.t = Hashtbl.create 255
    
  let add_potential_merge ch =
    let lit = List.hd ch.as_list in
    let former_potential_merges =
      try
        Hashtbl.find potential_merge lit
      with
        Not_found -> IdSet.empty
    in
    Format.(fprintf err_formatter "@[Adding %a for merge with lit %i@]@."
              pp_id ch.id lit
    );
    Hashtbl.replace potential_merge lit
    @@ IdSet.add ch.id former_potential_merges

  let remove_potential_merge ch = 
    let lit = List.hd ch.as_list in
    let former_potential_merges =
      try
        Hashtbl.find potential_merge lit
      with
        Not_found -> IdSet.empty in
    Hashtbl.replace potential_merge lit
    @@ IdSet.remove ch.id former_potential_merges
    
          
  let exists (i,s) = try 
    let ti = Hashtbl.find global i in
    Hashtbl.mem ti s 
    with Not_found -> false

  let not_rat (i,s) = try 
    let ti = Hashtbl.find global i in
    let ch = Hashtbl.find ti s in
    IdMap.is_empty ch.rats
    with Not_found -> false

  let add ch =
    Format.(fprintf err_formatter "@[Adding clause %a@]@."
              pp_id ch.id 
    );
    assert (not @@ not_rat ch.id);
    let (i, s) = ch.id in
    if not @@ IdMap.is_empty ch.rats then
      add_potential_merge ch;
    let ti =
      try Hashtbl.find global i
      with Not_found -> let ti = Hashtbl.create 255 in
                        Hashtbl.add global i ti; ti
    in
    Hashtbl.add ti s ch;
    Ptset.iter (fun j ->
      Format.(fprintf err_formatter "@[Adding reverse %i -> %i@]@."
              j i 
      );
      let s' = try Hashtbl.find reverse j with Not_found -> Ptset.empty in
      Hashtbl.replace reverse j (Ptset.add i s')) s
      
      
  let replace ch =
    Format.(fprintf err_formatter "@[Replacing clause %a@]@."
              pp_id ch.id 
    );
    let (i, s) = ch.id in
    if not @@ IdMap.is_empty ch.rats then
      add_potential_merge ch;
    let ti =
      try Hashtbl.find global i
      with Not_found -> let ti = Hashtbl.create 255 in
                        Hashtbl.add global i ti; ti
    in
    assert (Hashtbl.mem ti s);
    Hashtbl.replace ti s ch

  let find (i, s) =
    let ti = Hashtbl.find global i in
    Hashtbl.find ti s

  let iter_all (i, s) f =
    if Ptset.is_empty s then
    let ti = Hashtbl.copy (Hashtbl.find global i) in
    Hashtbl.iter (fun s' ch ->
      assert (ch.id = (i,s'));
      f ch) ti

  let remove_sub i j =
    try let ti = Hashtbl.find global i in
    Hashtbl.filter_map_inplace
      (fun s ch -> if Ptset.mem j s then None else Some ch) ti
    with Not_found -> ()
      
  let remove_all (i,s) =
    (try  Ptset.iter (fun j ->
      Format.(fprintf err_formatter "sub_deleting %i in %i@." i j);
      remove_sub j i) (Hashtbl.find reverse i)
    with Not_found -> ());
    begin try
      let ti = Hashtbl.find global i in
      Hashtbl.iter
        (fun _ ci ->
          if not @@ IdMap.is_empty ci.rats then
            remove_potential_merge ci) ti
    with Not_found -> () end;
    assert (Ptset.is_empty s);
    Format.(fprintf err_formatter "@[Deleting clause %a@]@."
              pp_id (i,s) 
    );
    Hashtbl.remove global i

  let potential_merges l =
    try
      Hashtbl.find potential_merge l
    with Not_found -> IdSet.empty

end  

    

module type AuxMap = sig
  type t
  val create : int -> t
  val add : t -> id -> id -> clause_hist -> unit
  val find : t -> id -> id -> clause_hist
  val find_or_add : t -> id -> id -> (id -> id -> clause_hist) -> clause_hist
end

module AM : AuxMap = struct
  type t = (id, (id, clause_hist) Hashtbl.t) Hashtbl.t

  let create i = Hashtbl.create i

  let add t i j c =
    try
      let cm = Hashtbl.find t i in
      Hashtbl.add cm j c
    with Not_found ->
      let cm = Hashtbl.create 11 in
      Hashtbl.add cm j c;
      Hashtbl.add t i cm

  let find t i j =
      let cm = Hashtbl.find t i in
      Hashtbl.find cm j

  let find_or_add t i j f =
    try
      find t i j
    with Not_found ->
      let c = f i j in
      add t i j c;
      c
end
  
let aux_clause_map = AM.create 255
  
  
let array_of_list_map f = function
    [] -> [||]
  | hd::tl as l ->
      let a = Array.make (List.length l) (f hd) in
      let rec fill i = function
          [] -> a
        | hd::tl -> Array.unsafe_set a i (f hd); fill (i+1) tl in
      fill 1 tl

exception Need_rat of lit * id

let rec concrete_arg e j c =
  let ch = CM.find (merge_ids j c.id) in
  if IdMap.is_empty ch.rats then
    ch
  else
    match Env.find (List.hd ch.as_list) e with
    | From_clause j' -> concrete_arg e j' ch
    | From_self j' ->
       let base = base_id (fst j') in
       if IdMap.mem base ch.rats then
         let ch' = CM.find (merge_ids ch.id base) in
         ch' 
       else
       raise (Need_rat(List.hd ch.as_list, ch.id))
    | From_pred | From_rat _ -> failwith "Not implemented"
        
let rec arg_from_env e c i =
  try
    match Env.find i e with
      From_clause _ | From_self _ -> Lit i
    | From_pred -> Pred i
    | From_rat j -> begin
      try
        let ch = concrete_arg e j c in
        let new_e = Env.add (-i) From_pred e in
        Rcstr (i, make_core new_e ch)
      with Not_found ->
        let open Format in
        fprintf err_formatter "From: Cannot find RAT clause %a vs %a@." pp_id c.id pp_id j;
        failwith "make_core" end
  with
    Not_found ->
      let open Format in
      fprintf err_formatter "Literal %i not found in current environment:\n@[<v>" i;
      pp_env err_formatter e;
      fprintf err_formatter "@]@.";
      failwith "Not found"
        
and make_core e ch =
  assert (IdMap.is_empty ch.rats); (* do not use RAT clause in proofs *)
  Core (ch.id,
        array_of_list_map (arg_from_env e ch) ch.as_list)

let unit_propagation c invmodel =
  List.fold_left (fun cr i -> Ptset.remove i cr)
    c invmodel
    

exception Not_a_tautology
exception Tautology of lit
exception No_need_RAT
  
(* proof a tautology,
   @requires for at least one l of lits, not l is in d
 *)
let rec make_tautology lits d =
  match lits with
    [] -> raise Not_a_tautology
  | l :: q ->
     if Ptset.mem (-l) d
     then Tauto l
     else make_tautology q d
       
  

let push_decl ct =
  Format.(fprintf Globals.dedukti_out "%a@." Proof_steps.pp_clause_term ct)


let rec split_rup rup id =
  match rup with
    [] -> [], []
  | x::q when x = id -> [], q
  | x::q -> let b,e = split_rup q id in
            x::b, e

let remove_rev i l =
  let rec remove_rev_aux i accu = function
    | [] -> accu
    | x::q -> if i = x then remove_rev_aux i accu q else
        remove_rev_aux i (x::accu) q
  in
  remove_rev_aux i [] l
    
    
let rec rup_rat e invmodel = function
  | [] -> failwith "No RUP"
  | i::q ->
     let ci = CM.find i in
     let propagated = unit_propagation ci.clause invmodel in
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
         let new_invmodel = (-new_lit)::invmodel in
         find_concrete ci e new_lit new_invmodel q
     | None -> 
        if IdMap.is_empty ci.rats
        then (* parent is a RUP clause *)
          Qed (make_core e ci)
        else
          let first_lit = List.hd ci.as_list in
          match  Env.find first_lit e with
            From_clause first_lit_from ->
              let ch = 
                try
                  CM.find (merge_ids i first_lit_from)
                with Not_found ->
                  let open Format in
                  fprintf err_formatter "To: Cannot find RAT clause %a vs %a@." pp_id i pp_id first_lit_from;
                  failwith "make_core"
              in
              Qed (make_core e ch)
          | From_self _ ->
             raise (Need_rat(first_lit, i))
          | From_pred | From_rat _ -> failwith "ohoh"


and find_concrete ci e new_lit new_invmodel q =
  if IdMap.is_empty ci.rats
  then (* parent is a RUP clause *)
    let new_e_pred = Env.add new_lit From_pred e in
    let new_e_lit = Env.add (-new_lit) (From_clause ci.id) e in
    Let_o (-new_lit, make_core new_e_pred ci,
           rup_rat new_e_lit new_invmodel q)
  else
    let first_lit = List.hd ci.as_list in
    if first_lit = new_lit then
      let new_e_lit = Env.add (-new_lit) (From_rat ci.id) e in
      rup_rat new_e_lit new_invmodel q
    else
      match  Env.find first_lit e with
        From_clause first_lit_from ->
          let ch = 
            try
              CM.find (merge_ids ci.id first_lit_from)
            with Not_found ->
              Format.(fprintf err_formatter "To: Cannot find RAT clause %a vs %a@." pp_id ci.id pp_id first_lit_from);
              failwith "make_core"
          in
          find_concrete ch e new_lit new_invmodel q
      | From_self _ -> raise (Need_rat(first_lit, ci.id))
      | From_pred -> failwith "ohoh"
      | From_rat k ->
         assert (CM.not_rat @@ merge_ids ci.id k);
        let ch = 
          CM.find (merge_ids ci.id k)
        in
        find_concrete ch e new_lit new_invmodel q
(*

  let new_e_lit = Env.add (-new_lit) (From_rat (merge_ids k ci.id)) e in
  rup_rat new_e_lit new_invmodel q
*)

          
and make_rat crat coth =
  let first_lit = List.hd crat.as_list in
  if not @@ Ptset.mem (-first_lit) coth.clause then raise No_need_RAT
  else
    try
      let sides = IdMap.find coth.id crat.rats in
      try
        merge_rat crat coth (crat.rup @ sides)
      with
        Not_found -> failwith "dzdaj"
    with
      Not_found ->
        merge_rat crat coth @@ update_rup_with_rat crat coth.id coth.rup
          

and update_rup_with_rat crat tocreate_id rup  =
  List.map
    (fun i ->
      if i = crat.id then
        (fst tocreate_id, Ptset.singleton (fst crat.id))
      else begin
        assert (CM.exists i);
        let ci = CM.find i in
        if Ptset.mem (-List.hd crat.as_list) ci.clause then
          let bid = base_id (fst i) in
          let cbid = CM.find bid in
          if Ptset.mem (List.hd crat.as_list) cbid.clause then
            bid
          else
            merge_ids crat.id i
        else
          i end)
    rup

    
and merge_rat crat coth rup =
  assert (crat.as_list <> []);
  let first_lit = List.hd crat.as_list in
  assert (Ptset.mem (-first_lit) coth.clause);
  let coth_minus = Ptset.remove (-first_lit) coth.clause in
  let crat_minus =
    Ptset.fold (fun l c ->
      let bid = base_id (fst coth.id) in
      let cbid = CM.find bid in
      if Ptset.mem l cbid.clause then c else
      Ptset.remove (-l) c) coth_minus crat.clause
  in
  let clause = Ptset.union crat_minus coth_minus in
  let as_list = Ptset.fold (fun i l -> i::l) clause [] in
  let id = merge_ids crat.id coth.id in
  assert (not @@ CM.not_rat id);
  let c = { id; clause; as_list; rats = IdMap.empty; rup } in
  begin
    Format.(fprintf err_formatter "Merging clauses %a and %a@."
              pp_cid crat.id
              pp_cid coth.id);
    c
  end
    
and prepare_rup c =
  let r =  try
             let invmodel = c.as_list in
             let e = List.fold_left (fun e i ->
               if Env.mem (-i) e then raise (Tautology i)
               else Env.add i (From_self c.id) e)
               Env.empty c.as_list in
             rup_rat e invmodel c.rup
    with
      Tautology i -> Tauto i
  in
  do_potential_merges c;
  r
    
and do_potential_merges c =
  let potential_merges =
    List.fold_left
      (fun pm i ->
        try
          IdSet.union (CM.potential_merges @@ -i) pm
        with
          Not_found -> pm)
      IdSet.empty c.as_list in
  Format.(fprintf err_formatter "@[Potential merges for %a:" pp_id c.id);
  IdSet.iter (Format.(fprintf err_formatter " %a" pp_id)) potential_merges;
  Format.(fprintf err_formatter "@]@.");
  IdSet.iter
    (fun j ->
        if not @@ occurs_in_id j c.id then 
        try
          let _ =
            Format.(fprintf err_formatter "potential merge %a %a@." pp_id c.id pp_id j) in
          let crat = try CM.find  j
            with Not_found -> Format.(fprintf err_formatter "Not_found : %a@." pp_cid j); raise Not_found
          in
          if IdMap.is_empty c.rats then
            if CM.not_rat @@ merge_ids crat.id c.id then () else
              try
                let c_merge = make_rat crat c in
                let new_crat =
                  { crat with rats = IdMap.add c.id [] crat.rats } in
                CM.replace new_crat;
                (*AM.add aux_clause_map j c.id c_merge;*)
                CM.add c_merge;
                push_or_virtual c_merge
              with Not_found -> failwith "pate"
              | No_need_RAT -> Format.(fprintf err_formatter "No need to do %a" pp_id @@ merge_ids crat.id c.id)
          else
            if CM.exists @@ merge_ids crat.id c.id then ()
            (* already there, and RAT *)
            else 
            try
              Format.(fprintf err_formatter "New RAT clause : %a vs %a@." pp_cid crat.id pp_cid c.id);
              let cv = virtual_rat crat c in
              CM.add cv;
              do_potential_merges cv;
            (* IdMap.iter
               (fun i p ->
               let ci = CM.find i in
               if CM.exists @@ merge_ids crat.id c.id then () else
               let c = make_rat cv ci in
               CM.add c;
               (*AM.add aux_clause_map cv.id i c;*)
               push_or_virtual c
               )
               c.rats *)
            with Not_found -> failwith "en croute"
        with
          Not_found -> (* j is no longer in the global table, so it is probably not needed *)
            Format.(fprintf err_formatter "failed merge %a %a@." pp_id c.id pp_id j))
    potential_merges

and virtual_rat crat coth =
  let first_lit_crat = List.hd crat.as_list in
  let first_lit_coth = List.hd coth.as_list in
  let coth_minus = Ptset.remove first_lit_coth @@
    Ptset.remove (-first_lit_crat) coth.clause in
  let clause_minus = Ptset.union crat.clause coth_minus in
  let as_list_minus = Ptset.fold (fun i l -> i::l) clause_minus [] in
  let as_list = first_lit_coth :: as_list_minus in
  let clause = Ptset.add first_lit_coth clause_minus in
  let id = merge_ids crat.id coth.id in
  let rup = update_rup_with_rat crat coth.id coth.rup in
  let filtered_rats = IdMap.filter (fun id _ -> CM.exists id) coth.rats in
  let rats = IdMap.map (update_rup_with_rat crat coth.id) filtered_rats in
  { id; clause; as_list; rats; rup }

and push_or_virtual ch =
  try
    push_decl @@ Let_clause(ch.id, ch.as_list, prepare_rup ch)
  with
    Need_rat(i,rat_id) ->
      Format.(fprintf err_formatter "Virtual RAT clause %a with %i and %a.@."
                pp_id ch.id i pp_id rat_id
      );
        (* if Ptset.is_empty @@ snd ch.id then *)
        let crat = CM.find rat_id in
        let begin_rup, end_rup = split_rup ch.rup rat_id in
        let new_rats = IdMap.mapi (fun k _ -> merge_ids rat_id k::
          List.map (fun j ->
            let cj = CM.find j in
            if not @@ IdMap.is_empty cj.rats && i = List.hd cj.as_list
            then merge_ids j k
            else j)
          end_rup)
          crat.rats in
        let new_clause =
          { ch with as_list = i::(remove_rev i ch.as_list);
            rup = begin_rup;
            rats = new_rats
          }
        in
        CM.replace new_clause;
        do_potential_merges new_clause;
        IdMap.iter
          (fun i p ->
            if not @@ occurs_in_id i ch.id then
              try
                let ci = CM.find i in
                if CM.not_rat @@ merge_ids ch.id ci.id then
                  Format.(fprintf err_formatter "Not doing %a@." pp_id ci.id)
                else
                  let c = make_rat new_clause ci in
                  CM.add c;
                (*AM.add aux_clause_map ch.id i c;*)
                  push_or_virtual c
              with
                Not_found ->
          (* clause i has been deleted *) ()
              | Need_rat _ -> failwith "hs"
          )
          new_clause.rats
(*      else
        begin Format.(fprintf err_formatter "No adding virtual clause@.");
          raise No_need_RAT end
*)
    
let define_clauses ch =
  Format.(fprintf err_formatter "Beginning clause %a@."
                  pp_id ch.id);
  if IdMap.is_empty ch.rats then
    push_or_virtual ch
  else begin
    do_potential_merges ch; 
    IdMap.iter
      (fun i p ->
        Format.(fprintf err_formatter "RATing %a@."
                  pp_id i);
(*        CM.iter_all i (fun ci ->          
          Format.(fprintf err_formatter "Trying %a@."
          pp_id ci.id); *)
        let ci = CM.find i in        
        if CM.not_rat @@ merge_ids ch.id ci.id then
          Format.(fprintf err_formatter "Not doing %a@." pp_id ci.id)
        else
          try let c = make_rat ch ci in
              CM.add c;
              push_or_virtual c
          with No_need_RAT -> ()
      )
      ch.rats 
  end
