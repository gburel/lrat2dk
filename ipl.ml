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
    Let_clause of id * lit list * proof_term

open Format

let pp_cid ppf i = fprintf ppf "c%a" pp_id i

let pp_termpred ppf i = if i > 0 then
    fprintf ppf "tp%d" i
  else
    fprintf ppf "tl%d" (-i)

let pp_termlit ppf i = if i > 0 then
    fprintf ppf "tl%d" i
  else
    fprintf ppf "tnl%d" (-i)

let pp_not_lit ppf i = if i > 0 then
    fprintf ppf "(not p%d)" i
  else
    fprintf ppf "(not (not p%d))" (-i)

let pp_liftpred ppf i = if i > 0 then
    fprintf ppf "tl%d" i
  else
    fprintf ppf "(lift p%d tp%d)" (-i) (-i)

      
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
     fprintf ppf "@[let_clause@ %a @]@[("
       pp_clause_par_dk l;
     List.iter (fprintf ppf "%a =>@ " pp_termlit) l;
     fprintf ppf "@[<2>%a@])@]" pp_proof_term pt;
     incr nb_parens;
     fprintf ppf "(%a =>@." pp_cid i

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
       fprintf ppf "@[def %a@ :@ @[embed %a@] :=@]@."
         pp_cid i
         pp_clause_par_dk l;
      List.iter (fprintf ppf "@[%a =>@ " pp_termlit) l;
      fprintf ppf "@[%a@]@].@."pp_proof_term pt

  let end_proof ppf last_id =
    fprintf ppf "@[def proof : eps bot := %a.@]@." pp_cid last_id

end
      
         
