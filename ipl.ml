open Lrat_types

type core = Core of id * arg array
and arg =
    Lit of lit   (* witness of a literal *)
  | Pred of lit  (* witness of a predicate *)
  | Rcstr of lit * core  (* reconstruction of the proof due to RAT *)

type proof_term =
    Let_o of lit * core * proof_term
  | Qed of core
  | Tauto of lit
      
type clause_term =
    Let_clause of id * clause * proof_term
  | Declare_clause of id * clause
  | Extended_lit_def of extended_lit * lit * clause
  | Implied_clause of extended_clause * extended_lit * clause
  | Subst_clause of extended_clause * lit * extended_lit * clause
      
open Format

let declare_preds ppf l u = 
  for i = l to u do
    fprintf ppf "p%d : o.@." i
  done;
  Globals.max_pred := u

let pp_termpred ppf i = if i > 0 then
    fprintf ppf "tp%d" i
  else
    fprintf ppf "tl%d" (-i)

let pp_termlit ppf i = if i > 0 then
    fprintf ppf "tl%d" i
  else
    fprintf ppf "tnl%d" (-i)

let pp_not_lit ppf i =
  fprintf ppf "(not %a)" pp_lit_dk i


let pp_liftpred ppf i =
  if is_pos (find_extended_lit i) then
    pp_termpred ppf (-i)
  else
    fprintf ppf "(lift %a %a)" pp_lit_dk (-i) pp_termpred (-i)

      
let rec pp_core ppf = function
  Core (i, a) ->
  fprintf ppf "@[%a@ " pp_cid i;
  Array.iter (fprintf ppf "%a@ " pp_arg) a;
  fprintf ppf"@]"
and pp_arg ppf =  function
    Lit l -> pp_termlit ppf l
  | Pred l -> pp_liftpred ppf l
  | Rcstr (l, c) ->
     fprintf ppf "@[(%a => %a)@]"
       pp_termpred l
       pp_core c

let pp_subst_lit_dk p el ppf i =
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
  done
      
let rec pp_proof_term ppf = function
  | Let_o (l, t1, t2) ->
     fprintf ppf "@[let_o@ %a @]@ @[(%a =>@ %a)@]@ @[(%a =>@ %a)@]"
       pp_not_lit l
       pp_termpred l
       pp_core t1
       pp_termlit l
       pp_proof_term t2 
  | Qed c -> 
     pp_core ppf c
  | Tauto l ->
     let ln, lp = if l > 0 then -l, l else l, -l in
     fprintf ppf "@[%a %a@]" pp_termlit ln pp_termlit lp

module type PP = sig
  val begin_proof : formatter -> int -> unit
  val pp_clause_term : formatter -> clause_term -> unit
  val end_proof : formatter -> id -> unit
end
  
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

module Proof_steps : PP = struct
  let begin_proof ppf nb_clauses =
    for i = 1 to nb_clauses do
      fprintf ppf "@[c%d : embed C%d.@]@." i i
    done

  let pp_clause_term ppf = function
    | Let_clause (i, l, pt) ->
       fprintf ppf "@[thm %a@ :@ @[embed (%a)@]@ :=@]@."
         pp_cid i
         pp_clause_dk l;
      Ptset.fold (fun i _ -> fprintf ppf "@[%a =>@ " pp_termlit i) l ();
      fprintf ppf "@[%a@]@].@."pp_proof_term pt
    | Declare_clause (i, l) -> 
       fprintf ppf "@[%a@ :@ @[embed (%a)@].@]@."
         pp_cid i
         pp_clause_dk l
    | Extended_lit_def (i, p, c) -> 
       fprintf ppf "@[def %a@ :@ o@]@ :=@ @[<2>or %a (imp (and_clause (%a)) bot)@]."
         pp_el_dk i
         pp_lit_dk p
         pp_clause_dk c
    | Implied_clause (i, el, c) -> 
       fprintf ppf "@[%a@ :@ embed@ (add@ %a@ (%a))@]."
         pp_eid i
         pp_el_dk el
         pp_clause_dk c
    | Subst_clause (i, p, el, c) -> 
       fprintf ppf "@[%a@ :@ embed@ (%a)@]."
         pp_eid i
         (pp_subst_clause_dk p el) c
         
  let end_proof ppf last_id =
    fprintf ppf "@[thm proof : eps bot := %a.@]@." pp_cid last_id

end
      
         
