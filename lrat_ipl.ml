open Lrat_types
open Ipl

module IdSet = Set.Make(struct type t = id let compare = compare end)

let push_decl (Let_clause(i,_ ,_) as ct) =
  Format.(fprintf err_formatter "Pushing %a@." pp_id i);
  Format.(fprintf Globals.dedukti_out "%a@." Proof_steps.pp_clause_term ct)

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
  let as_list = Ptset.fold (fun i l -> i::l) clause [] in
  let ch = { id; clause; as_list; rup = []; rats = IdMap.empty } in
  push_decl (Let_clause(id, as_list, Tauto i));
  ch
             

module type ClauseMap =
sig
  val add : clause_hist -> unit
  val replace : clause_hist -> unit
  val find : id -> clause_hist
  val potential_merges : lit -> IdSet.t
  val remove : bool -> id -> unit
  val remove_all : id -> unit
  val exists : id -> bool
  val not_rat : id -> bool
  val mem_clause : clause -> bool
  val not_rat_clause : clause -> bool
  val add_id : id -> clause -> unit
  val link_id : id -> clause -> unit
end

module CM : ClauseMap =
struct
  
  let clause_to_ch : (clause, clause_hist) Hashtbl.t = Hashtbl.create 255
  let id_to_clause : (id, clause) Hashtbl.t = Hashtbl.create 255
  let reverse : (int, IdSet.t) Hashtbl.t = Hashtbl.create 255
  let potential_merge : (lit, IdSet.t) Hashtbl.t = Hashtbl.create 255

  let exists id = Hashtbl.mem id_to_clause id
    
  let not_rat id =
    try
      let c = Hashtbl.find id_to_clause id in
      let ch = Hashtbl.find clause_to_ch c in
      IdMap.is_empty ch.rats
    with Not_found -> false

  let add_reverse i id =
    Format.(fprintf err_formatter "@[Reverse link %i -> %a@]@."
              i  pp_id id
    );
    let s =
      try
        Hashtbl.find reverse i
      with Not_found -> IdSet.empty
    in
    Hashtbl.replace reverse i (IdSet.add id s) 

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

  let add_id id c = 
    Format.(fprintf err_formatter "@[Adding id %a@]@."
              pp_id id 
    );
    Hashtbl.add id_to_clause id c;
    iter_id (fun i -> add_reverse i id) id

  let add ch =
    add_id ch.id ch.clause;
    Format.(fprintf err_formatter "@[Adding clause %a@]@."
              pp_id ch.id 
    );
    if not_rat ch.id then 
      Format.(fprintf err_formatter "@[Warning: clause %a already present as %a@]@."
                pp_id ch.id  pp_id (Hashtbl.find clause_to_ch ch.clause).id
      );
    Hashtbl.add clause_to_ch ch.clause ch;
    if not @@ IdMap.is_empty ch.rats then
      add_potential_merge ch
        
  let replace ch =
    Format.(fprintf err_formatter "@[Replacing clause %a@]@."
              pp_id ch.id 
    );
    (*assert (Hashtbl.mem clause_to_ch ch.clause);*)
    Hashtbl.replace clause_to_ch ch.clause ch;
    if not @@ IdMap.is_empty ch.rats then
      add_potential_merge ch

  let rec find_from_clauses id =
    match id with
      Base i -> raise Not_found
    | Quotient (a,b) ->
       let coth = find a in
       let crat = find b in
       let first_lit = List.hd crat.as_list in
       assert (Ptset.mem (-first_lit) coth.clause);
       let coth_minus = Ptset.remove (-first_lit) coth.clause in
       let clause = Ptset.union crat.clause coth_minus in
       let ch = try Hashtbl.find clause_to_ch clause
         with Not_found ->
           let ch = create_tauto id clause in
           add ch; 
           ch
       in
       add_id id ch.clause;
       ch
       
     
  and find id =
    try
      let c = Hashtbl.find id_to_clause id in
      Hashtbl.find clause_to_ch c
    with
      Not_found -> find_from_clauses id

  let remove_sub id =
    Format.(fprintf err_formatter "@ @[Sub deleting clause %a@]"
              pp_id id 
    );
    begin
    try
       let c = Hashtbl.find id_to_clause id in
       let ch = Hashtbl.find clause_to_ch c in
       if ch.id = id then remove_potential_merge ch
    with Not_found -> ()
    end;
    Hashtbl.remove id_to_clause id
    
        
  let remove_all id =
    Format.(fprintf err_formatter "@[<v2>Deleting clause %a"
              pp_id id 
    );
    begin
    match id with
    | Quotient _ -> failwith "Trying to remove non base clause"
    | Base i ->
       try
         let s = Hashtbl.find reverse i in
         IdSet.iter remove_sub s
       with Not_found -> () end;
    Format.(fprintf err_formatter "@]@.")
         
  (*TODO : remove potential merges *)

  let remove not_the_clause id =
    let clause = Hashtbl.find id_to_clause id in
    Hashtbl.remove id_to_clause id;
    if not not_the_clause then Hashtbl.remove clause_to_ch clause
      
  let potential_merges l =
    try
      Hashtbl.find potential_merge l
    with Not_found -> IdSet.empty

  let not_rat_clause c =
    try
      let ch = Hashtbl.find clause_to_ch c
      in IdMap.is_empty ch.rats && Hashtbl.mem id_to_clause ch.id
    with 
      Not_found -> false

  let mem_clause c =
    try
      let ch = Hashtbl.find clause_to_ch c
      in Hashtbl.mem id_to_clause ch.id
    with 
      Not_found -> false
        
  let link_id id c =
    let ch = Hashtbl.find clause_to_ch c in
    Format.(fprintf err_formatter "@[<v2>Associating %a with %a@]@."
              pp_id id  pp_id ch.id
    );
    add_id id ch.clause
      
end  

    
  
  
let array_of_list_map f = function
    [] -> [||]
  | hd::tl as l ->
      let a = Array.make (List.length l) (f hd) in
      let rec fill i = function
          [] -> a
        | hd::tl -> Array.unsafe_set a i (f hd); fill (i+1) tl in
      fill 1 tl

exception Need_rat of lit * id
exception Not_RUP
exception Delay of id
    
(** obtain_concrete : env -> clause_hist -> clause_hist
   return a non-RAT clause using the environment to cut RAT clauses
   @raises Need_rat if the cutting comes from the clause to construct *)
let rec obtain_concrete e ch =
  if IdMap.is_empty ch.rats then
    ch
  else
    match Env.find (List.hd ch.as_list) e with
    | From_clause j' | From_rat j' ->
       begin
         assert (CM.exists @@ merge_ids ch.id j');
         let ch' = CM.find (merge_ids ch.id j') in
         obtain_concrete e ch'
       end
    | From_self j' ->
       begin
         match j' with
         | Quotient (base,_) when IdMap.mem base ch.rats ->
            let ch' = CM.find (merge_ids ch.id base) in
            obtain_concrete e ch'
         | _ -> 
             raise (Need_rat(List.hd ch.as_list, ch.id))
       end         
    | From_pred ->
       raise (Delay ch.id)
    | From_subrat _ -> failwith "Not implemented"
        
let rec arg_from_env e cid i =
  try
    match Env.find i e with
      From_clause _ | From_self _ -> Lit i
    | From_pred -> Pred i
    | From_rat j ->
       begin
         let ch = 
                    CM.find @@ merge_ids j cid
         in
         let ch' = obtain_concrete e ch in
         let new_e = Env.add (-i) From_pred e in
         Rcstr (i, make_core new_e ch')
       end
    | From_subrat j ->
       begin
         let ch = CM.find j in
         let ch' = obtain_concrete e ch in
         let new_e = Env.add (-i) From_pred e in
         Rcstr (i, make_core new_e ch')
       end
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
        array_of_list_map (arg_from_env e ch.id) ch.as_list)

let unit_propagation c invmodel =
  List.fold_left (fun cr i -> Ptset.remove i cr)
    c invmodel
    

    
let rec split_rup rup id =
  match rup with
    [] -> [], []
  | x::q when is_in x id -> [], q
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
  | [] -> raise Not_RUP
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
          | From_self j ->
             (* look if the clause to be constructed was originally a RAT
                or a RUP clause *)
             begin
               match j with
                 Base _ -> raise (Need_rat(first_lit, ci.id))
               | Quotient (a,b) ->
                  let cb = CM.find b in
                  if IdMap.mem a cb.rats then
                    raise (Need_rat(first_lit, ci.id))
                  else 
                  (* first_literal of the RAT clause can nonetheless be obtained *)
                    let new_e_lit = Env.add (-first_lit) (From_rat i) e in
                    let new_invmodel = (-first_lit)::invmodel in
                    rup_rat new_e_lit new_invmodel q
             end
          | From_pred | From_rat _ | From_subrat _ -> failwith "ohoh"


and find_concrete ci e new_lit new_invmodel q =
  let new_e_pred = Env.add new_lit From_pred e in
  try
    let ch = obtain_concrete new_e_pred ci in
    let new_e_lit = Env.add (-new_lit) (From_clause ch.id) e in
    Let_o (-new_lit, make_core new_e_pred ch,
           rup_rat new_e_lit new_invmodel q)
  with
    Delay id -> 
      let new_e_lit = Env.add (-new_lit) (From_rat id) e in
      let new_e_lit = match id with
          Base _ -> new_e_lit
        | Quotient(a,b) ->
           let cb = CM.find b in
           let first_lit = List.hd cb.as_list in
           if Env.mem first_lit new_e_lit then
             new_e_lit
           else
             Env.add (List.hd cb.as_list) (From_subrat a) new_e_lit in
      rup_rat new_e_lit new_invmodel q

        

(*  if IdMap.is_empty ci.rats
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
    | From_self j' ->
    begin
    match j' with
    Base _ ->
    raise (Need_rat(first_lit, ci.id))
    | Quotient (base,_) -> 
    if IdMap.mem base ci.rats then
    let ch' = CM.find (merge_ids ci.id base) in
    find_concrete ch' e new_lit new_invmodel q
    else
    raise (Need_rat(first_lit, ci.id))
    (*         raise (Need_rat(List.hd ch.as_list, ch.id))*)
    end
    | From_pred -> failwith "ohoh"
    | From_rat k ->
    assert (CM.not_rat @@ merge_ids ci.id k);
    let ch = 
    CM.find (merge_ids ci.id k)
    in
    find_concrete ch e new_lit new_invmodel q*)
(*

  let new_e_lit = Env.add (-new_lit) (From_rat (merge_ids k ci.id)) e in
  rup_rat new_e_lit new_invmodel q
*)

        
and make_rat crat coth =
  let first_lit = List.hd crat.as_list in
  if not @@ Ptset.mem (-first_lit) coth.clause then None
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
        tocreate_id
      else begin
        (*        if not (CM.exists i) then raise Not_RUP; *)
        let ci = CM.find i in
        if Ptset.mem (-List.hd crat.as_list) ci.clause then
          let bid = get_base i in
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
  let clause = Ptset.union crat.clause coth_minus in
  let id = merge_ids crat.id coth.id in
  if CM.not_rat_clause clause
  then (CM.link_id id clause; None)
  else 
    let as_list = Ptset.fold (fun i l -> i::l) clause [] in
    let c = { id; clause; as_list; rats = IdMap.empty; rup } in
    begin
      Format.(fprintf err_formatter "Merging clauses %a and %a@."
                pp_cid crat.id
                pp_cid coth.id);
      Some c
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
              let already_there = CM.exists @@ merge_ids crat.id c.id in
              try
                match make_rat crat c with
                  None -> ()
                | Some c_merge -> 
                   begin
                     push_or_virtual c_merge;
                     if (CM.find crat.id).id <> c_merge.id then
                       let new_crat =
                         { crat with rats = IdMap.add c.id [] crat.rats } in
                       CM.replace new_crat
                   end
              with Not_found -> (Format.(fprintf err_formatter "Failed to construct clause %a vs %a@." pp_cid crat.id pp_cid c.id);
                                 CM.remove already_there @@ merge_ids crat.id c.id
              )
          else
            if CM.exists @@ merge_ids crat.id c.id then ()
            (* already there, and RAT *)
            else 
              begin
                Format.(fprintf err_formatter "New RAT clause : %a vs %a@." pp_cid crat.id pp_cid c.id);
                match virtual_rat crat c with
                  None -> ()
                | Some cv -> 
                   ((*Format.(fprintf err_formatter "Making RAT clauses@.");
                      IdMap.iter
                      (fun i p ->
                      if IdMap.mem i crat.rats then begin
                      Format.(fprintf err_formatter "RAT clause %a@." pp_id i);
                      let ci = CM.find (merge_ids crat.id i) in
                      if CM.exists @@ merge_ids c.id ci.id then () else
                      try match make_rat c ci with
                      None -> ()
                      | Some c -> 
                      (CM.add c;
                      push_or_virtual c)
                      with Not_RUP -> ()
                      end
                      else ())
                      c.rats;*)
                     CM.add cv;
                     do_potential_merges cv;
                   ) end
        with
          Not_found -> (* j is no longer in the global table, so it is probably not needed *)
            Format.(fprintf err_formatter "failed merge %a %a@." pp_id c.id pp_id j))
    potential_merges

and virtual_rat crat coth =
  let first_lit_crat = List.hd crat.as_list in
  let first_lit_coth = List.hd coth.as_list in
  let id = merge_ids crat.id coth.id in
  if first_lit_crat = - first_lit_coth then
    let clause = Ptset.union (Ptset.remove first_lit_coth coth.clause) crat.clause in
    assert (CM.mem_clause clause);
    CM.link_id id clause;
    None
  else
    let coth_minus = Ptset.remove first_lit_coth @@
      Ptset.remove (-first_lit_crat) coth.clause in
    let clause_minus = Ptset.union crat.clause coth_minus in
    let as_list_minus = Ptset.fold (fun i l -> i::l) clause_minus [] in
    let as_list = first_lit_coth :: as_list_minus in
    let clause = Ptset.add first_lit_coth clause_minus in
    if CM.mem_clause clause
    then (CM.link_id id clause; None)
    else 
      let rup = update_rup_with_rat crat coth.id coth.rup in
      let filtered_rats = IdMap.filter (fun id _ -> CM.exists id) coth.rats in
      let rats = IdMap.map (update_rup_with_rat crat coth.id) filtered_rats in
      Some { id; clause; as_list; rats; rup }

and push_or_virtual ch =
  try
    Format.(fprintf err_formatter "Trying to push %a@." pp_id ch.id);
    begin
      try
        push_decl @@ Let_clause(ch.id, ch.as_list, prepare_rup ch);
        Format.(fprintf err_formatter "Pushed %a@." pp_id ch.id);
        CM.add ch;
        do_potential_merges ch
      with
        Not_RUP ->
          Format.(fprintf err_formatter "Not able to construct %a@." pp_id ch.id);
    end;
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
          if (not (IdMap.is_empty cj.rats)) && i = List.hd cj.as_list
          then Format.(fprintf err_formatter "updating %a %a@." pp_id cj.id pp_id k; merge_ids cj.id k)
          else j)
        end_rup)
        crat.rats in
      let new_rats = IdMap.filter (fun j _ -> CM.exists j) new_rats in
      let new_clause =
        { ch with as_list = i::(remove_rev i ch.as_list);
          rup = begin_rup;
          rats = new_rats
        }
      in
      CM.add new_clause; 
      do_potential_merges new_clause; 
      IdMap.iter
        (fun i p ->
          if not @@ occurs_in_id i ch.id then 
            begin
              Format.(fprintf err_formatter "VRATing %a@."
                        pp_id i);
              (*          if not @@ occurs_in_id i ch.id then*)
              if CM.exists i then 
                let ci = CM.find i in
                if CM.not_rat @@ merge_ids ch.id ci.id then
                  Format.(fprintf err_formatter "Not doing %a@." pp_id ci.id)
                else
                  match make_rat new_clause ci with
                    None -> ()
                  | Some c -> 
                     Format.(fprintf err_formatter "Was here %a@." pp_id c.id);
                    push_or_virtual c;
            end
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
    IdMap.iter
      (fun i p ->
        Format.(fprintf err_formatter "RATing %a@."
                  pp_id i);
        (* CM.iter_all i (fun ci -> Format.(fprintf err_formatter
           "Trying %a@."  pp_id ci.id); *)
        if CM.not_rat @@ merge_ids ch.id i then
          Format.(fprintf err_formatter "Not doing %a@." pp_id i)
        else
          let ci = CM.find i in        
          match make_rat ch ci with
            None -> ()
          | Some c -> 
             push_or_virtual c
      )
        ch.rats;
        do_potential_merges ch
  end
