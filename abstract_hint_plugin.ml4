(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    /   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Names
open Tacmach
open Tacticals
open Tactics
open Term
open Termops

let get_fresh_theorem_name prefix =
  Namegen.next_global_ident_away (id_of_string prefix) (Pfedit.get_all_proof_names ())

(****************)
let my_occur_var id c =
  let rec occur_rec c =
    match kind_of_term c with
    | Var i -> if id == i then raise Occur
    | _ -> iter_constr occur_rec c
  in
  try occur_rec c; false with
    Occur -> true


let occur_id id c =
  (my_occur_var id c) || not (noccurn 1 c)


(*
  Implements the delayed generalisation algorithm to remove superflous assumptions from a cached lemma
 *)
let rec remove_unused_lambdas r ty =
  match kind_of_term r, kind_of_term ty with
  | Lambda (name,t,c), Prod (pa,pb,pc) ->
      let (l,c,pc) = remove_unused_lambdas c pc in
      let (lambda_used, lambda_usedp) = (match name with
        Name id ->
	  (* Check if the lambda term is used. As the lambda term variable could be referred
	     to with Rel, we cannot just check for Var id terms. *)
	  occur_id id c, occur_id id pc
      | Anonymous ->
	  not (noccurn 1 c), not (noccurn 1 c)) in
      (if lambda_used || lambda_usedp then
	(* Keep this lambda term *)
	(false::l,mkLambda (name, t, c), mkProd (pa,pb,pc))
      else
	(* Remove this lambda term. *)
	(true::l, (lift (-1) c), (lift (-1) pc)))
  | _ ->  ([],r,ty)

(* Tactic that takes a list of bools, and introduces the
 * hypotheses corresponding to the true values (leaving
 * the ones corresponding to false in the goal. *)
let rec intro_specified l =
  match l with
  | [] -> tclIDTAC
  | b :: l -> (intro_then (fun id ->
      let tac = intro_specified l in
      if b then tac
      else tclTHEN tac (revert [id])))

(* Adds a cached lemma to suitable lemma databases *)
let auto_add_hint id bases g =
  let add_hints_iff l2r lc n bl =
    Auto.add_hints false bl (Auto.HintsResolveEntry (List.map (fun x -> (n, l2r,
									 None, x)) lc)) in
  (let priority = Some 0 (* "trivial" will only use priority 0 rules *) in
  add_hints_iff false [(Constrintern.global_reference id)] priority bases)

(* Stores the proof for g as name in base if the tactic proves g *)
(* TODO: don't cache if the lemma exists already *)
let lemma_cache ?(add_as_hint=true) prefix solving_tactic bases g =
  let name = get_fresh_theorem_name (prefix ^ "_temp") in
  (* If we can evaluate t, we know the lemma has been solved and cached *)
  let t = tclABSTRACT (Some name) solving_tactic g in
  ignore(t); (* keeping this for if we want to add an option to not optimise proofs *)

  (* Get the proof term and type of the cached lemma *)
  let cached_constant = (Constrintern.global_reference (name)) in
  let cached_type = pf_type_of g cached_constant in
  let cached_term = Indfun_common.def_of_const cached_constant in

  let concl_nprod = nb_prod (pf_concl g) in
  let type_nprod = nb_prod cached_type in
  (* Use delayed generalisation algorithm on proof term  *)
  let (l,optimised_term,optimised_type) = remove_unused_lambdas cached_term cached_type in

  (* Add the optimised proof term as a new definition *)
  let save_theorem prefix theorem_type theorem_term =
    let id = get_fresh_theorem_name prefix in
    let ce =
      { Entries.const_entry_body = theorem_term;
        const_entry_type = Some theorem_type;
        const_entry_opaque = false}
    in
    ignore (Declare.declare_constant id (Entries.DefinitionEntry ce, Decl_kinds.IsDefinition (Decl_kinds.Scheme)));
    id in

  let id = save_theorem prefix optimised_type optimised_term in

  if add_as_hint then auto_add_hint id bases g;

  (* Solve this subgoal using the optimised proof o. It is important to not use the unoptimised proof term as the latter
     may use superflous assumptions, which then makes it impossible for these to be removed from the top-level cached lemma *)
  let (_,l) = Util.list_chop (type_nprod - concl_nprod) l in
  tclTHEN (intro_specified l)
    (apply (Constrintern.global_reference (id)))
    g

TACTIC EXTEND abstract_hint
  | [ "abstract_hint" "[" preident_list(bases) "]" tactic(t)]
    -> [ lemma_cache "userhint" (Tacinterp.eval_tactic t) bases]
  | [ "abstract_hint" ident(name) "[" preident_list(bases) "]" tactic(t)]
    -> [ lemma_cache (string_of_id name) (Tacinterp.eval_tactic t) bases]
END
