open Lrat_types

type core =
    Core of extended_id * arg array
  | Proj of extended_lit * extended_lit (* projection of a extended definition *)
and arg =
    Lit of extended_lit   (* witness of a literal *)
  | Pred of extended_lit  (* witness of a predicate *)

type proof_term =
    Let_o of extended_lit * core * proof_term
  | Qed of core
  | Tauto of extended_lit
  | Let_extended of extended_lit (* new lit *) * extended_lit (* pivot *)
    * clause (* remainder *) * proof_term
  | Extended of extended_lit * clause (* remainder *)
  | New of extended_lit * clause (* remainder *)

type clause_term =
    Let_clause of extended_id * clause * proof_term
  | Declare_clause of extended_id * clause
  | Extended_lit_def of extended_lit * lit * clause
  | New_lit_def of extended_lit * clause

open Format

let declare_preds ppf l u =
  for i = l to u do
    fprintf ppf "p%d : o.@." i
  done

let pp_termpred ppf i = if is_pos i then
    fprintf ppf "tp%a" pp_el_dk i
  else
    fprintf ppf "tl%a" pp_el_dk (neg_el i)

let pp_termlit ppf i = if is_pos i then
    fprintf ppf "tl%a" pp_el_dk i
  else
    fprintf ppf "tnl%a" pp_el_dk (neg_el i)

let pp_not_lit ppf i =
  fprintf ppf "(not %a)" pp_el_dk i

let pp_liftpred ppf i =
  if is_pos i then
    pp_termpred ppf (neg_el i)
  else
    fprintf ppf "(lift %a %a)" pp_el_dk (neg_el i) pp_termpred (neg_el i)


let rec pp_core ppf = function
  | Core (i, a) ->
  fprintf ppf "@[%a@ " pp_eid i;
  Array.iter (fprintf ppf "%a@ " pp_arg) a;
  fprintf ppf"@]"
  | Proj (l, r) ->
     fprintf ppf "@[%a@ (_ =>@ %a =>@ _ =>@ %a@ %a)@]"
       pp_termlit l
       pp_termlit r
       pp_termlit r
       pp_termpred r
and pp_arg ppf =  function
    Lit l -> pp_termlit ppf l
  | Pred l -> pp_liftpred ppf l

(*let pp_subst_lit_dk p el ppf i =
  if i = p then pp_el_dk ppf el
  else pp_lit_dk ppf i

let pp_subst_clause_dk p el ppf c =
  let nb_par = Ptset.fold (fun lit i ->
    if i > 0 then fprintf ppf "(";
    fprintf ppf "add@ %a@ "
      (pp_subst_lit_dk p el) lit;
    i+1) c 0 in
  fprintf ppf "empty";
  for i = 2 to nb_par do
    fprintf ppf ")"
  done*)

let rec pp_proof_term s ppf = function
  | Let_o (l, t1, t2) ->
     fprintf ppf "@[let_o@ %a @]@ @[(%a =>@ %a)@]@ @[(%a =>@ %a)@]"
       pp_not_lit l
       pp_termpred l
       pp_core t1
       pp_termlit l
       (pp_proof_term s) t2
  | Qed c ->
     pp_core ppf c
  | Tauto l ->
     let ln, lp = if is_pos l then neg_el l, l else l, neg_el l in
     fprintf ppf "@[%a %a@]" pp_termlit ln pp_termlit lp
  | Let_extended (x, p, r, t) ->
     fprintf ppf "@[%a@ (x => x@ bot@ %a@ (y => y ("
       pp_termlit x
       pp_termlit p
    ;
    Ptset.fold (fun i _ ->
      let l = find_extended_lit s i in
      fprintf ppf "%a@ =>@ "
        pp_termpred (neg_el l)
    ) r ();
    Ptset.fold (fun i _ ->
      let l = find_extended_lit s i in
      if not @@ is_pos l then
      fprintf ppf "@[let_o@ %a@ %a@ (%a =>@ "
        pp_not_lit l
        pp_liftpred l
        pp_termlit l
    ) r ();
    fprintf ppf "@]@ %a)))" (pp_proof_term s) t;
    Ptset.fold (fun i _ -> let l = find_extended_lit s i in
      if not @@ is_pos l then fprintf ppf ")@]") r ();
  | Extended (x, r) ->
     let nb_neg =
       Ptset.fold (fun i n ->
         let l = find_extended_lit s i in
         if is_pos l then n else
           begin
             fprintf ppf "%a@ @[(%a =>@ "
               pp_termlit l
               pp_termpred (neg_el l);
             n+1
           end) r 0 in
     fprintf ppf "%a@ (z => _ => rem => rem@ (a => a"
       pp_termlit x;
     Ptset.fold (fun i _ ->
         let l = find_extended_lit s i in
         fprintf ppf "@ %a" pp_termpred (neg_el l)) r ();
     fprintf ppf "))";
     for i = 1 to nb_neg do fprintf ppf ")@]" done
  | New (x, r) ->
     let nb_neg =
       Ptset.fold (fun i n ->
         let l = find_extended_lit s i in
         if is_pos l then n else
           begin
             fprintf ppf "%a@ @[(%a =>@ "
               pp_termlit l
               pp_termpred (neg_el l);
             n+1
           end) r 0 in
     fprintf ppf "%a@ (rem => rem"
       pp_termlit x;
     Ptset.fold (fun i _ ->
         let l = find_extended_lit s i in
         fprintf ppf "@ %a" pp_termpred (neg_el l)) r ();
     fprintf ppf ")";
     for i = 1 to nb_neg do fprintf ppf ")@]" done


module type PP = sig
  val begin_proof : formatter -> int -> unit
  val pp_clause_term : subst -> formatter -> clause_term -> unit
  val end_proof : subst-> formatter -> id -> unit
end

  (*
module One_proof_term : PP =
struct
  let nb_parens = ref 0

  let begin_proof ppf nb_clauses =
    fprintf ppf "@[<hov2>def proof :@ @[";
    for i = 1 to nb_clauses do
      fprintf ppf "embed C%d@ ->@ @[" i
    done;
    fprintf ppf "eps bot";
    for i = 1 to nb_clauses do
      fprintf ppf "@]"
    done;
    fprintf ppf "@]@ :=@ @]@.@[";
    for i = 1 to nb_clauses do
      fprintf ppf "c%d => " i
    done;
    fprintf ppf "@]@.";
    nb_parens := 0


  let pp_clause_term ppf = function
  | Let_clause (i, l, pt) ->
     fprintf ppf "@[let_clause@ (%a) @]@[("
       pp_clause_dk l;
     Ptset.fold (fun i _ -> fprintf ppf "%a =>@ " pp_termlit i) l ();
     fprintf ppf "@[<2>%a@])@]" pp_proof_term pt;
     incr nb_parens;
     fprintf ppf "(%a =>@." pp_cid i
  | _ -> failwith "Declaration of clauses not allowed in one-proof format"

  let end_proof ppf last_id =
    pp_cid ppf last_id;
    for i = 1 to !nb_parens do
        fprintf ppf ")"
    done;
    fprintf ppf ".@."

end
  *)

module Proof_steps : PP = struct
  let begin_proof ppf nb_clauses =
    for i = 1 to nb_clauses do
      fprintf ppf "@[c%d : embed C%d.@]@." i i
    done

  let pp_clause_term s ppf = function
    | Let_clause (i, l, pt) ->
       fprintf ppf "@[thm %a@ :@ @[embed (%a)@]@ :=@]@."
         pp_eid i
         (pp_clause_dk s) l;
      Ptset.fold (fun i _ -> fprintf ppf "%a =>@ " pp_termlit (find_extended_lit s i)) l ();
      fprintf ppf "@[%a@]@].@." (pp_proof_term s) pt
    | Declare_clause (i, l) ->
       fprintf ppf "@[%a@ :@ @[embed (%a)@].@]@."
         pp_eid i
         (pp_clause_dk s) l
    | Extended_lit_def (i, p, c) ->
       fprintf ppf "@[def %a@ :@ o@]@ :=@ @[<2>or %a (imp (and_clause (%a)) bot)@].@."
         pp_el_dk i
         (pp_lit_dk s) p
         (pp_neg_clause_dk s) c
    | New_lit_def (p, c) ->
       fprintf ppf "@[def %a@ :@ o@]@ :=@ @[<2>imp (and_clause (%a)) bot@].@."
         pp_el_dk  p
         (pp_neg_clause_dk s) c


  let end_proof s ppf last_id =
    fprintf ppf "@[thm proof : eps bot := %a.@]@." (pp_cid s) last_id

end
