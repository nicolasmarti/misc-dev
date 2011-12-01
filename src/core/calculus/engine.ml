open Def
open Misc
open Context
open Libparser
open Substitution
open Printf
open Pprinter
open Extlist

(*************************************************************)
(*      unification/reduction, type{checking/inference}      *)
(*************************************************************)


let debug = ref false

let debug_oracles = ref false

(*
  reduction of terms
  several strategy are possible:
  for beta reduction: Lazy or Eager
  possibility to have strong beta reduction
  delta: unfold destructors (replace cste with their destructors)
  iota: try to match destructors l.h.s
  deltaiotaweak: if after delta reduction (on head of app), a iota reduction fails, then the delta reduction is backtracked
  deltaiotaweak_armed: just a flag to tell the reduction function that it should raise a IotaReductionFailed
  zeta: compute the let bindings
  eta: not sure if needed

  all these different strategy are used for several cases: unification, typechecking, ...
  
*)

(* for now only eager is implemented !!!*)
type strategy = 
  | Lazy 
  | Eager

type reduction_strategy = {
  beta: strategy;
  betastrong: bool;
  delta: bool;
  iota: bool;
  deltaiotaweak: bool;
  deltaiotaweak_armed: bool;
  zeta: bool;
  eta: bool;
}

(* the default strategy for typechecking/unification/ ...*)
let unification_strat : reduction_strategy = {
  beta = Eager;
  betastrong = false;
  delta = true;
  iota = true;
  deltaiotaweak = false;
  deltaiotaweak_armed = false;
  zeta = true;
  eta = true;
}

(* a special exception for the reduction which 
   signals that an underlying iota reduction fails
*)
exception IotaReductionFailed

(* unification pattern to term *)
(*
  Three possibility
  * either unification is possible, in which case the context is updated with the proper unifier, and we return a unified terms
  * either unification is impossible, in which case we return a NoUnification exception
  * or we do not know if unification is possible or not, in which case we return a UnknownUnification exception
  
  this last case is caught, and we try to ask oracles if they can prove that the term are equal (actually, just that if for any predicate they are undistinguisheable, in which case the UnknownUnification become the empty unification) or different (equality implies False)
*)

(*
  this is a updateable list of oracles: basically functions which are given a defs, a context, and a term ty, and which purpose is to find a term which has type ty
*)

let unification_oracles_list : ((defs * context * term) -> term option) list ref = ref []

(*
 
  equality ty1 ty2 :=
  
  (P: type(ty1) -> Type) -> P(ty1) -> P(ty2)

  inequality ty1 ty2 :=
  
  equality ty1 ty2 -> (Q: Type) -> Q

*)

let rec term_equality (defs: defs) (ctxt: context ref) (ty1: term) (ty2: term) : term =
  let pname = Name "P" in  
  let pty = TVar (add_fvar ctxt (Type nopos), nopos) in
  let te = Impl ((pname, pty, Explicit, nopos), 
		 Impl ((Symbol ("_", Nofix), App (TVar (0, nopos), [(shift_term ty1 1, Explicit)], nopos), Explicit, nopos),
		       App (TVar (1, nopos), [(shift_term ty2 2, Explicit)], nopos)
		       , nopos), nopos) in
  let te, _ = typecheck defs ctxt te (Type nopos) in
  te

and term_inequality (defs: defs) (ctxt: context ref) (ty1: term) (ty2: term) : term =
  let te = Impl ((Name "H", term_equality defs ctxt ty1 ty2, Explicit, nopos),
		 Impl ((Name "Q", Type nopos, Explicit, nopos),
		       TVar (0, nopos), nopos), nopos) in
  let te, _ = typecheck defs ctxt te (Type nopos) in
  te

and unification_pattern_term (ctxt: context) (p: pattern) (te:term) : substitution =
  match p, te with
    | PType _, Type _-> IndexMap.empty
    | PVar (n, ty, _), te -> IndexMap.singleton 0 te
    | PAVar _, te -> IndexMap.empty
    | PCste (s1, _), Cste (s2, _) when s1 = s2 -> IndexMap.empty
    | PCste (s1, _), Cste (s2, _) when s1 <> s2 -> raise (DoudouException (NoMatchingPattern (ctxt, p, te)))
    | PAlias (n, p, ty, _), te ->
      (* grab the substitution *)
      let s = unification_pattern_term ctxt p te in
      (* shift it by one (for the n of the alias) *)
      let s = shift_substitution s 1 in
      (* we put in the substitution the shifting of te by |s| + 1 at index 0 *)
      IndexMap.add 0 te s
    (* for the application, we only accept same constante as head and same number of arguments 
       this is really conservatives .. we could implement the same mechanism as in subtitution_term_term
    *)
    | PApp ((s1, _), args1, ty, _), App (Cste (s2, _), args2, _) when List.length args1 = List.length args2 && s1 = s2 ->
      (* we unify arguments one by one (with proper shifting) *)
      List.fold_left (fun s ((arg1, n1), (arg2, n2)) -> 
	(* first we unify both args *)
	let s12 = unification_pattern_term ctxt arg1 arg2 in
	(* we need to shift the accumulator by the number of introduced free variable == caridnality of s12 *)
	IndexMap.fold (fun k value acc -> IndexMap.add (k + IndexMap.cardinal s12) value acc) s s12
      ) IndexMap.empty (List.combine args1 args2)

    | _ -> raise (DoudouException (NoMatchingPattern (ctxt, p, te)))

and unification_term_term (defs: defs) (ctxt: context ref) (te1: term) (te2: term) : term =
  if !debug then printf "unification: %s Vs %s\n" (term2string !ctxt te1) (term2string !ctxt te2);
  let res = (
    try (
      match te1, te2 with

	(* the error cases for AVar and TName *)
	| AVar _, _ -> raise (DoudouException (FreeError "unification_term_term catastrophic: AVar in te1 "))
	| _, AVar _ -> raise (DoudouException (FreeError "unification_term_term catastrophic: AVar in te2 "))
	| TName _, _ -> raise (DoudouException (FreeError "unification_term_term catastrophic: TName in te1 "))
	| _, TName _ -> raise (DoudouException (FreeError "unification_term_term catastrophic: TName in te2 "))


	(* the trivial cases for Type, Cste and Obj *)
	| Type p1, Type p2 -> Type (best_pos p1 p2)
	| Obj (o1, p1), Obj (o2, p2) when o1 = o2 -> Obj (o1, best_pos p1 p2)
	| Obj (o1, p1), Obj (o2, p2) when o1#equal o2 -> Obj (o1, best_pos p1 p2)
	| Cste (c1, p1), Cste (c2, p2) when c1 = c2 -> Cste (c1, best_pos p1 p2)

	(* the trivial case for variable *)
	| TVar (i1, p1), TVar (i2, p2) when i1 = i2 -> TVar (i1, best_pos p1 p2)

	| TVar (i1, p1), TVar (i2, p2) when i1 < 0 && i2 < 0 -> 
	  let imin = min i1 i2 in
	  let imax = max i1 i2 in
	  let s = IndexMap.singleton imin (TVar (imax, best_pos p1 p2)) in
	  ctxt := context_substitution s (!ctxt);
	  TVar (imax, best_pos p1 p2)

	(* in other cases, the frame contains the value for a given bound variable. If its not itself, we should unfold *)
	| TVar (i1, p1), _ when i1 >= 0 && set_term_pos (bvar_value !ctxt i1) nopos <> TVar (i1, nopos) ->
	  let _ = unification_term_term defs ctxt (bvar_value !ctxt i1) te2 in
	  TVar (i1, p1)

	| _, TVar (i2, p2) when i2 >= 0 && set_term_pos (bvar_value !ctxt i2) nopos <> TVar (i2, nopos) ->
	  let _ = unification_term_term defs ctxt te1 (bvar_value !ctxt i2) in
	  TVar (i2, p2)

	(* the case for free variables *)
	(* we need the free var to not be a free var of the term *)
	| TVar (i1, p1), _ when i1 < 0 && not (IndexSet.mem i1 (fv_term te2)) -> (
	  let s = IndexMap.singleton i1 te2 in
	  ctxt := context_substitution s (!ctxt);
	  te2      
	)
	| _, TVar (i2, p2) when i2 < 0 && not (IndexSet.mem i2 (fv_term te1))->
	  let s = IndexMap.singleton i2 te1 in
	  ctxt := context_substitution s (!ctxt);
	  te1

	(* cases for constantes *)
	| Cste (c1, pos), _ -> (
	  match unfold_constante defs c1 with
	    (* c1 is an inductive, a constructor or an axiom, we should have the strict equality with te2 *)
	    | Inductive _ | Axiom | Constructor -> 
	      if set_term_pos (reduction defs ctxt unification_strat te2) nopos = Cste (c1, nopos) then
		Cste (c1, pos)
	      else
		raise (DoudouException (NoUnification (!ctxt, te1, te2)))
	    (* if just one equation, we might want to unfold *)
	    | Equation [PCste (c2, _), te] when c1 = c2 ->
	      unification_term_term defs ctxt te te2
	    (* these case is impossible *)
	    | Equation [PCste (c2, _), te] when c1 <> c2 ->
	      raise (DoudouException (FreeError "Catastrophic: an equation for a constante has a different constante symbol"))
	    (* more than one equation ... we do not now *)
	    | Equation _ ->
	      raise (DoudouException (UnknownUnification (!ctxt, te1, te2)))
	)

	| _, Cste (c2, pos) -> (
	  match unfold_constante defs c2 with
	    (* c1 is an inductive, a constructor or an axiom, we should have the strict equality with te2 *)
	    | Inductive _ | Axiom | Constructor -> 
	      if set_term_pos (reduction defs ctxt unification_strat te1) nopos = Cste (c2, nopos) then
		Cste (c2, pos)
	      else
		raise (DoudouException (NoUnification (!ctxt, te1, te2)))
	    (* if just one equation, we might want to unfold *)
	    | Equation [PCste (c1, _), te] when c1 = c2 ->
	      unification_term_term defs ctxt te1 te 
	    (* these case is impossible *)
	    | Equation [PCste (c1, _), te] when c1 <> c2 ->
	      raise (DoudouException (FreeError "Catastrophic: an equation for a constante has a different constante symbol"))
	    (* more than one equation ... we do not now *)
	    | Equation _ ->
	      raise (DoudouException (UnknownUnification (!ctxt, te1, te2)))
	)

	(* the impl case: only works if both are impl *)
	| Impl ((s1, ty1, n1, pq1), te1, p1), Impl ((s2, ty2, n2, pq2), te2, p2) ->
	  (* the symbol is not important, yet the nature is ! *)
	  if n1 <> n2 then raise (DoudouException (NoUnification (!ctxt, te1, te2))) else
	    (* we unify the types *)
	    let ty = unification_term_term defs ctxt ty1 ty2 in
	    (* we push the quantification *)
	    push_quantification (s1, ty, n1, pq1) ctxt;
	    (* we need to substitute te1 and te2 with the context substitution (which might have been changed by unification of ty1 ty2) *)
	    let s = context2substitution !ctxt in
	    let te1 = term_substitution s te1 in
	    let te2 = term_substitution s te2 in
	    (* we unify *)
	    let te = unification_term_term defs ctxt te1 te2 in
	    (* we pop quantification *)
	    let q1, [te] = pop_quantification ctxt [te] in
	    (* and we return the term *)
	    Impl (q1, te, p1)
	      
	(* the Lambda case: only works if both are Lambda *)
	| Lambda ((s1, ty1, n1, pq1), te1, p1), Lambda ((s2, ty2, n2, pq2), te2, p2) ->
	  (* the symbol is not important, yet the nature is ! *)
	  if n1 <> n2 then raise (DoudouException (NoUnification (!ctxt, te1, te2))) else
	    (* we unify the types *)
	    let ty = unification_term_term defs ctxt ty1 ty2 in
	    (* we push the quantification *)
	    push_quantification (s1, ty, n1, pq1) ctxt;
	    (* we need to substitute te1 and te2 with the context substitution (which might have been changed by unification of ty1 ty2) *)
	    let s = context2substitution !ctxt in
	    let te1 = term_substitution s te1 in
	    let te2 = term_substitution s te2 in
	    (* we unify *)
	    let te = unification_term_term defs ctxt te1 te2 in
	    (* we pop quantification *)
	    let q1, [te] = pop_quantification ctxt [te] in
	    (* and we return the term *)
	    Lambda (q1, te, p1)

	(* some higher order unification *)
	| App (TVar (i, p1), (arg, n)::args, p2), t2 when i < 0 ->
	  if !debug then printf "unification case: | App (TVar (i, p1), (arg, n)::args, p2), _ -> \n" ;
	  (* here the principle is to "extract" the arg from the other term, transforming it into a Lambda and retry the unification *)
	  (* shift te 1 : now there is no TVar 0 in te *)
	  let te2 = shift_term te2 1 in
	  (* thus we can rewrite (shift arg 1) by TVar 0 *)
	  let te2 = rewrite_term defs !ctxt (shift_term arg 1) (TVar (0, nopos)) te2 in
	  (* we just verify that we have some instance of TVar 0 *)
	  if not (IndexSet.mem 0 (bv_term te2)) then raise (DoudouException (UnknownUnification (!ctxt, te1, t2)));
	  (* we rebuild the lambda *)
	  let arg, ty = typeinfer defs ctxt arg in
	  let te2 = Lambda ((Symbol ("_", Nofix), ty, n, nopos), te2, nopos) in
	  (* and now we continue without the arguments *)
	  let res = unification_term_term defs ctxt (App (TVar (i, p1), args, p2)) te2 in
	  let res = App (res, [arg, n], nopos) in
	  let res = reduction defs ctxt unification_strat res in
	  res

	| t1, App (TVar (i, p1), (arg, n)::args, p2) when i < 0  ->
	  if !debug then printf "unification case: | App (TVar (i, p1), (arg, n)::args, p2), _ -> \n" ;
	  (* here the principle is to "extract" the arg from the other term, transforming it into a Lambda and retry the unification *)
	  (* shift te 1 : now there is no TVar 0 in te *)
	  let te1 = shift_term te1 1 in
	  (* thus we can rewrite (shift arg 1) by TVar 0 *)
	  let te1 = rewrite_term defs !ctxt (shift_term arg 1) (TVar (0, nopos)) te1 in
	  (* we just verify that we have some instance of TVar 0 *)
	  if not (IndexSet.mem 0 (bv_term te1)) then raise (DoudouException (UnknownUnification (!ctxt, t1, te2)));
	  (* we rebuild the lambda *)
	  let arg, ty = typeinfer defs ctxt arg in
	  let te1 = Lambda ((Symbol ("_", Nofix), ty, n, nopos), te1, nopos) in
	  (* and now we continue without the arguments *)
	  let res = unification_term_term defs ctxt (App (TVar (i, p1), args, p2)) te1 in
	  let res = App (res, [arg, n], nopos) in
	  let res = reduction defs ctxt unification_strat res in
	  res

	(* the case of two application: with not the same arity *)
	| App (hd1, args1, p1), App (hd2, args2, p2) when List.length args1 <> List.length args2 ->
	  if !debug then printf "unification case: | App (hd1, args1, p1), App (hd2, args2, p2) when List.length args1 <> List.length args2 -> \n" ;
	  (* first we try to change them such that they have the same number of arguments and try to match them *)
	  let min_arity = min (List.length args1) (List.length args2) in
	  let te1' = if List.length args1 = min_arity then te1 else (
	    let pos1 = fst (get_term_pos hd1) in
	    let largs1 = take (List.length args1 - min_arity) args1 in
	    let largs2 = drop (List.length args1 - min_arity) args1 in
	    let pos2 = snd (get_term_pos (fst (last largs1))) in
	    let pos3 = snd (get_term_pos (fst (last largs2))) in
	    App (App (hd1, largs1, (pos1, pos2)), largs2, (pos1, pos3))
	  ) in
	  let te2' = if List.length args2 = min_arity then te2 else (
	    let pos1 = fst (get_term_pos hd2) in
	    let largs1 = take (List.length args2 - min_arity) args2 in
	    let largs2 = drop (List.length args2 - min_arity) args2 in
	    let pos2 = snd (get_term_pos (fst (last largs1))) in
	    let pos3 = snd (get_term_pos (fst (last largs2))) in
	    App (App (hd2, largs1, (pos1, pos2)), largs2, (pos1, pos3))
	  ) in
	  (* we save the current context somewhere to rollback *)
	  let saved_ctxt = !ctxt in
	  (try 
	     unification_term_term defs ctxt te1' te2' 
	   with
	     (* apparently it does not work, so we try to reduce them *)
	     | DoudouException err ->
	       if !debug then printf "%s\n" (error2string err);
	       (* restore the context *)
	       ctxt := saved_ctxt;
	       (* reducing them *)
	       let te1' = reduction defs ctxt unification_strat te1 in
	       let te2' = reduction defs ctxt unification_strat te2 in
	       (* if both are still the sames, we definitely do not know if they can be unify, else we try to unify the new terms *)
	       if eq_term te1 te1' && eq_term te2 te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2'
	  )
	(* the case of two application with same arity *)
	| App (hd1, args1, p1), App (hd2, args2, p2) when List.length args1 = List.length args2 ->
	  if !debug then printf "unification case: | App (hd1, args1, p1), App (hd2, args2, p2) when List.length args1 = List.length args2 -> \n" ;
	  (* first we save the context and try to unify all term component *)
	  let saved_ctxt = !ctxt in
	  (try
	     (* we need to push the arguments (through this we also verify that the nature matches ) *)
	     (* we build a list where arguments of te1 and te2 are alternate *)
	     let rev_arglist = List.fold_left (
	       fun acc ((arg1, n1), (arg2, n2)) ->
		 if n1 <> n2 then
		   (* if both nature are different -> no unification ! *)
		   raise (DoudouException (NoUnification (!ctxt, te1, te2)))
		 else  
		   arg2::arg1::acc
	     ) [] (List.combine args1 args2) in
	     let arglist = List.rev rev_arglist in
	     (* and we push this list *)
	     push_terms ctxt arglist;
	     (* first we unify the head of applications *)
	     let hd = unification_term_term defs ctxt hd1 hd2 in
	     (* then we unify all the arguments pair-wise, taking them from the list *)
	     let args = List.map (fun (_, n) ->
	       (* we grab the next argument for te1 and te2 in the context (and we know that their nature is equal to n) *)
	       let [arg1; arg2] = pop_terms ctxt 2 in
	       (* and we unify *)
	       let arg = unification_term_term defs ctxt arg1 arg2 in
	       (arg, n)
	     ) args1 in
	     (* finally we have our unified term ! *)
	     App (hd, args, best_pos p1 p2)

	   with
	     (* apparently it does not work, so we try to reduce them *)
	     | DoudouException err ->
	       if !debug then printf "%s\n" (error2string err);
	       (* restore the context *)
	       ctxt := saved_ctxt;
	       (* reducing them *)
	       let te1' = reduction defs ctxt unification_strat te1 in
	       let te2' = reduction defs ctxt unification_strat te2 in
	       (* if both are still the sames, we definitely do not know if they can be unify, else we try to unify the new terms *)
	       if eq_term te1 te1' && eq_term te2 te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2'
	  )	
	(* the cases where only one term is an Application: we should try to reduce it if possible, else we do not know! *)
	| App (hd1, args1, p1), _ ->
	  if !debug then printf "unification case: App (hd1, args1, p1), _ -> \n" ;
	  let te1' = reduction defs ctxt unification_strat te1 in
	  if eq_term te1 te1' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2
	| _, App (hd2, args2, p2) ->
	  if !debug then printf "unification case: | _, App (hd2, args2, p2) -> \n" ;
	  let te2' = reduction defs ctxt unification_strat te2 in
	  if eq_term te2 te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1 te2'

	(* for all the rest: I do not know ! *)
	| _ -> 
	  (* I am really not sure here ... *)
	  if true then (
	    (* reducing them *)
	    let te1' = reduction defs ctxt unification_strat te1 in
	    let te2' = reduction defs ctxt unification_strat te2 in
	    (* if both are still the sames, we definitely do not know if they can be unify, else we try to unify the new terms *)
	    if eq_term te1 te1' && eq_term te2 te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2'
	  )
	  else raise (DoudouException (UnknownUnification (!ctxt, te1, te2)))
    ) with
      | DoudouException (UnknownUnification (ctxt', te1', te2')) as e when eq_term te1 te1' && eq_term te2 te2' -> (
	try (
	(* in this case we ask oracles if they can decide equality or inequality *)
	  let ctxt' = ref ctxt' in
	(* first let test equality *)
	  let equality_assertion = term_equality defs ctxt' te1 te2 in
	  if !debug_oracles then printf "unification ask to oracles: %s\n" (term2string !ctxt equality_assertion);
	  let equality_result = fold_stop (fun () oracle ->
	    match oracle (defs, !ctxt', equality_assertion) with
	      | None -> Left ()
	      | Some prf ->
	      (* we check the proof *)
		try 
		  let _ = typecheck defs ctxt' prf equality_assertion in
		  Right ()
		with
		  | _ -> Left ()
	  ) () !unification_oracles_list in
	  match equality_result with
	    | Right _ ->
	    (* we have a proof of equality, we can return the term te1 *)
	      te1
	    | Left _ ->
	    (* no proof of equality, but maybe a proof of inequality *)
	      let inequality_assertion = term_inequality defs ctxt' te1 te2 in
	      if !debug_oracles then printf "unification ask to oracles: %s\n" (term2string !ctxt inequality_assertion);
	      let inequality_result = fold_stop (fun () oracle ->
		match oracle (defs, !ctxt', inequality_assertion) with
		  | None -> Left ()
		  | Some prf ->
		  (* we check the proof *)
		    try 
		      let _ = typecheck defs ctxt' prf inequality_assertion in
		      Right ()
		    with
		      | _ -> Left ()
	      ) () !unification_oracles_list in
	      match inequality_result with
		| Right _ ->
		(* we have a proof of inequality, we can return that the term cannot unify *)
		  raise (DoudouException (NoUnification (!ctxt', te1', te2')))
		| Left _ ->
		(* no proof of equality, but maybe a proof of inequality *)
		  raise e
	) with
	  | _ -> raise e
      )
      | e -> raise e	
  ) in
  if !debug then printf "unification result: %s\n" (term2string !ctxt res);
  res

and reduction (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  if !debug then printf "reduction: %s\n" (term2string !ctxt te);
  let res = (
  match te with

    | Type _ -> te
    (* without delta reduction we do unfold *)
    | Cste (c1, _) when not strat.delta -> te


    (* with delta reduction we unfold *)
    | Cste (c1, _) when strat.delta -> (
      match unfold_constante defs c1 with
	| Equation [PCste (c2, _), te] when c1 = c2 -> te
	| Equation [PCste (c2, _), te] when c1 <> c2 ->
	  raise (DoudouException (FreeError "Catastrophic: an equation for a constante has a different constante symbol"))
	| _ -> te
    )

    | Obj _ -> te

    (* for both free and bound variables we have their value in the context *)
    | TVar (i, _) when i >= 0 -> te
    | TVar (i, _) when i < 0 && set_term_pos (fvar_value !ctxt i) nopos <> TVar (i, nopos) -> fvar_value !ctxt i
    | TVar (i, _) when i < 0 -> te

    (* trivial error cases *) 
    | AVar _ -> raise (DoudouException (FreeError "reduction catastrophic: AVar"))
    | TName _ -> raise (DoudouException (FreeError "reduction catastrophic: TName"))

    (* Impl: we reduce the type, and the term only if betastrong *)
    | Impl ((s, ty, n, pq1), te, p1) -> 
      let ty = reduction defs ctxt strat ty in
      if strat.betastrong then (
	(* we push the quantification *)
	push_quantification (s, ty, n, pq1) ctxt;
	(* we reduce the body *)
	let te = reduction defs ctxt strat te in
	(* we pop the quantification *)
	let q1, [te] = pop_quantification ctxt [te] in
	(* and we return the term *)
	Impl (q1, te, p1)

      ) else Impl ((s, ty, n, pq1), te, p1)

    (* lambda: the eta expansion cases *)
    | Lambda ((s, _, n1, _), App (hd, [TVar (0, _), n2], _), _) when n1 = n2 && strat.eta &&
							       not (IndexSet.mem 0 (bv_term hd))
							     ->
      reduction defs ctxt strat (shift_term hd (-1))

    (* Lambda: we reduce the type, and the term only if betastrong *)
    | Lambda ((s, ty, n, pq), te, p) -> 
      let ty = reduction defs ctxt strat ty in
      if strat.betastrong then (
	(* we push the quantification *)
	push_quantification (s, ty, n, pq) ctxt;
	(* we reduce the body *)
	let te = reduction defs ctxt strat te in
	(* we pop the quantification *)
	let q1, [te] = pop_quantification ctxt [te] in
	(* and we return the term *)
	Lambda (q1, te, p)

      ) else Lambda ((s, ty, n, pq), te, p)
    
    (* Application: the big part *)
    (* for no only Eager is implemented *)
    | App _ when strat.beta = Eager -> (

      (* we do a case analysis ... *)
      match te with

	| App (hd, [], _) ->
	  reduction defs ctxt strat hd

	| App (Lambda ((s, ty, n, p1), te, p), (hd, _)::tl, p2) -> (

	  let hd = reduction defs ctxt strat hd in
	  let te = shift_term (term_substitution (IndexMap.singleton 0 (shift_term hd 1)) te) (-1) in
	  match tl with
	    | [] -> reduction defs ctxt strat te
	    | _ -> reduction defs ctxt strat (App (te, tl, (fst (get_term_pos te), snd p2)))

	)

	| App (Obj (o, _), args, _) -> (
	  let args = List.map (fun (arg, n) -> reduction defs ctxt strat arg, n) args in
	  reduction defs ctxt strat (o#apply defs !ctxt args)
	)

	(* a first subcase for app: with a Cste as head *)
	(* in case of deltaiota weakness, we need to catch the IotaReductionFailed exception *) 
	| App (Cste (c1, pos), args, pos2) -> (
	  match unfold_constante defs c1 with
	    | Equation eqs -> (
	      (* we reduce the arguments *)
	      let args = List.map (fun (arg, n) -> reduction defs ctxt strat arg, n) args in
	      (* we try all the possible equations *)
	      let res = fold_stop (fun () (p, body) ->
	      (* we could check that n = argn, but it should have been already checked *)
	      (* can we unify the pattern ? *)
		try 
		  let pargs_length = begin 
		    match p with 
		      | PApp (_, pargs, _, _) -> List.length pargs
		      | _ -> 0
		  end in
		  let neededargs = take pargs_length args in
		  let surplusargs = drop pargs_length args in
		  let cutterm = if pargs_length = 0 then Cste (c1, pos) else (App (Cste (c1, pos), neededargs, nopos)) in
		  let r = unification_pattern_term !ctxt p cutterm in
		  let te = term_substitution r body in
		  match surplusargs with
		    | [] -> Right te
		    | _ -> Right (App (te, surplusargs, (fst (get_term_pos te), snd (get_term_pos (fst (last surplusargs))))))
		with
		  | DoudouException (NoMatchingPattern (ctxt, p, te)) -> 
		    Left ()
	      ) () eqs in
	      match res with
		| Left () -> if strat.deltaiotaweak_armed then raise IotaReductionFailed else te
		| Right te -> reduction defs ctxt strat te
	    )
	    | _ -> App (Cste (c1, pos), List.map (fun (arg, n) -> reduction defs ctxt strat arg, n) args, pos2)
	)

	(* App is right associative ... *)
	| App (App (te1, args1, p1), arg2, p2) ->
	  reduction defs ctxt strat (App (te1, args1 @ arg2, (fst p1, snd p2)))

	| App (hd, args, p) ->
	  App (hd, List.map (fun (arg, n) -> reduction defs ctxt strat arg, n) args, p)

    )
    | Match (te, eqs, p) -> (
      (* we reduce the term *)
      let te = reduction defs ctxt strat te in
      (* we try all the possible equations *)
      let res = fold_stop (fun () (p, body) ->
	(* we could check that n = argn, but it should have been already checked *)
	(* can we unify the pattern ? *)
	try 
	  let r = unification_pattern_term !ctxt p te in
	  let te = term_substitution r body in
	  Right (shift_term te (- (pattern_size p)))
	with
	  | DoudouException (NoMatchingPattern (ctxt, p, te)) -> 
	    Left ()
      ) () eqs in
      match res with
	| Left () -> if strat.deltaiotaweak_armed then raise IotaReductionFailed else te
	| Right te -> reduction defs ctxt strat te
    )
  ) in
  if !debug then printf "reduction result: %s\n" (term2string !ctxt res);
  res

(*
  helper function that detect if the number of implicit arguments
  N.B.: no modulo reduction ....
*)      
and nb_implicit_arguments (defs: defs) (ctxt: context ref) (te: term) : int =
  match reduction defs ctxt unification_strat te with
    | Impl ((_, _, Implicit, _), te, _) -> 1 + nb_implicit_arguments defs ctxt te
    | _ -> 0

and typecheck (defs: defs) (ctxt: context ref) (te: term) (ty: term) : term * term =
  if !debug then printf "typecheck: %s :: %s\n" (term2string !ctxt te) (term2string !ctxt ty);
  let res = (
  (* save the context *)
  let saved_ctxt = !ctxt in
  try (
  match te, ty with
    (* one basic rule, Type :: Type *)
    | Type p1, Type p2 -> Type p1 , Type p2

    (* here we should have the case for which you cannot rely on the inference *)
      
    (* the most basic typechecking strategy, 
       infer the type ty', typecheck it with Type (really needed ??) and unify with ty    
    *)
    | _, _ ->
      let te, ty' = typeinfer defs ctxt te in
      (* we try to detect if there is more implicite quantification in the infer type than the typechecked type *)
      if nb_implicit_arguments defs ctxt ty' > nb_implicit_arguments defs ctxt ty then (
	(* yes, we need to apply the term to a free variable *)
	let fvty = add_fvar ctxt (Type nopos) in
	let fvte = add_fvar ctxt (TVar (fvty, nopos)) in
	let te = App (te, [TVar (fvte, nopos), Implicit], nopos) in
	(* and we retypecheck *)
	typecheck defs ctxt te ty
      ) else (
	(* no: we typecheck normally *)
	push_terms ctxt [te];
	let ty = unification_term_term defs ctxt ty ty' in
	let [te] = pop_terms ctxt 1 in
	te, ty
      )
  ) with
    | DoudouException ((CannotTypeCheck _) as err) ->
      raise (DoudouException err)
    | DoudouException err ->
      ctxt := saved_ctxt;
      let te, inferedty = typeinfer defs ctxt te in
      raise (DoudouException (CannotTypeCheck (!ctxt, te, inferedty, ty, err)))
  ) in
  if !debug then printf "typecheck result: %s :: %s\n" (term2string !ctxt (fst res)) (term2string !ctxt (snd res));
  res

and typeinfer (defs: defs) (ctxt: context ref) (te: term) : term * term =
  if !debug then printf "typeinfer: %s :: ???\n" (term2string !ctxt te);
  let res = (
  (* save the context *)
  let saved_ctxt = !ctxt in
  try (
  match te with
    | Type _ -> te, Type nopos

    | Cste (c1, _) -> te, constante_type defs c1

    | Obj (o, _) -> te, o#get_type

    | TVar (i, _) when i >= 0 -> te, bvar_type !ctxt i
    | TVar (i, _) when i < 0 -> te, fvar_type !ctxt i

    | TName (s, pos) -> (
      (* we first look for a bound variable *)
      match bvar_lookup !ctxt s with
	| Some i -> 
	  let te = TVar (i, pos) in
	  let ty = bvar_type !ctxt i in
	  te, ty
	| None -> 
	  (* we look for a constante *)
	  let te = Cste (constante_symbol defs s, pos) in
	  let ty = constante_type defs s in
	  te, ty
    )

    | Impl ((s, ty, n, pq), te, p) -> 
      (* first let's be sure that ty :: Type *)
      let ty, _ = typecheck defs ctxt ty (Type nopos) in
      (* we push the quantification *)
      push_quantification (s, ty, n, pq) ctxt;
      (* we typecheck te :: Type *)
      let te, ty' = typecheck defs ctxt te (Type nopos) in
      (* we pop quantification *)
      let q1, [te] = pop_quantification ctxt [te] in
      (* and we returns the term with type Type *)
      Impl (q1, te, p), ty'

    | Lambda ((s, ty, n, pq), te, p) -> 
      (* first let's be sure that ty :: Type *)
      let ty, _ = typecheck defs ctxt ty (Type nopos) in
      (* we push the quantification *)
      push_quantification (s, ty, n, pq) ctxt;
      (* we typeinfer te *)
      let te, tety = typeinfer defs ctxt te in
      (* we pop quantification *)
      let q1, [te; tety] = pop_quantification ctxt [te; tety] in
      (* and we returns the term with type Type *)
      Lambda (q1, te, p), Impl (q1, tety, nopos)

    (* app will have another version in typecheck that might force more unification or creation of free variables *)
    | App (te, args, pos) -> 
      let te, ty = typeinfer defs ctxt te in
      (* we push the term te, and its type *)
      push_terms ctxt [te];
      push_terms ctxt [ty];
      (* ty is in the state *)
      let nb_args = fold_cont (fun nb_processed_args args ->
	(* first pop the type *)
	let [ty] = pop_terms ctxt 1 in
	(* ty is well typed ... we should be able to reduce it just in case *)
	let ty = (
	  match ty with
	    | Impl _ -> ty
	    | _ -> reduction defs ctxt unification_strat ty
	) in
	(* we should push the args with there nature ... *)
	let added, remaining_args, ty = (	  
	  match args, ty with
	    | [], _ -> raise (DoudouException (FreeError "typeinfer of App: catastrophic, we have an empty list !!!"))
	    (* lots of cases here *)
	    (* both nature are the same: this is our arguments *)
	    | (hd, n1)::tl, Impl ((s, ty, n2, pq), te, p) when n1 = n2 -> 
	      (* we push an image of the impl, so that we can grab a body which may have been changed by typechecking *)
	      push_terms ctxt [Impl ((s, ty, n2, pq), te, p)];
	      (* first let see if hd has the proper type *)
	      let hd, ty = typecheck defs ctxt hd ty in
	      (* we compute the type of the application:
		 we grab back from the term stack the te terms
		 we substitute the bound var 0 (s) by shifting of 1 of hd, and then reshift the whole term by - 1		 
	      *)
	      let [Impl (_, te, _)] = pop_terms ctxt 1 in
	      let ty = term_substitution (IndexMap.singleton 0 (shift_term hd 1)) te in
	      let ty = shift_term ty (-1) in
	      (* we push the arg and its nature *)
	      push_terms ctxt [hd];
	      push_nature ctxt n1;
	      (* and we returns the information *)
	      1, tl, ty
	    (* the argument is explicit, but the type want an implicit arguments: we add free variable *)
	    | (hd, Explicit)::tl, Impl ((s, ty, Implicit, _), te, _) -> 
	    (* we add a free variable of the proper type *)
	      let fv = add_fvar ctxt ty in
	      (* we compute the type of the application:
		 we substitute the bound var 0 (s) by the free variable, and then reshift the whole term by - 1
	      *)	      
	      if !debug then printf "typeinfer: missing an Implicit var => intorducing %s :: %s\n" (term2string !ctxt (TVar (fv, nopos))) (term2string !ctxt ty);

	      let ty = term_substitution (IndexMap.singleton 0 (TVar (fv, nopos))) te in
	      let ty = shift_term ty (-1) in


	      (* we push the arg and its nature *)
	      push_terms ctxt [TVar (fv, nopos)];
	      push_nature ctxt Implicit;
	      (* and we returns the information *)
	      1, args, ty
	    | (hd, n)::_, Impl ((s, ty, n2, _), te, _) -> 	      
	      let args = List.rev (map_nth (fun i ->
		let [arg] = pop_terms ctxt 1 in
		let n = pop_nature ctxt in
		(arg, n)
	      ) nb_processed_args) in
	      let [te] = pop_terms ctxt 1 in
	      raise (DoudouException (CannotInfer (!ctxt, App (te, args@[hd,n], (fst (get_term_pos te), snd (get_term_pos hd))), (FreeError "terms needs an Explicit argument, but receives an Implicit one"))))
	    (* a (God) forsaken case: the type is a free variable *)
	    | (hd, n)::_, TVar (i, _) when i < 0 -> 
	      (* we create free variables in order to "build" a type *)
	      let fv1 = add_fvar ctxt (Type nopos) in
	      let fv2 = add_fvar ctxt (Type nopos) in
	      let fv3 = add_fvar ctxt (TVar (fv2, nopos)) in
	      (* we create a substitution *)
	      let ty' = Impl ((Symbol ("_", Nofix), TVar (fv1, nopos), n, nopos), TVar (fv3, nopos), nopos) in
	      let s = IndexMap.singleton i ty' in
	      (* do the subsitution in the context *)
	      ctxt := context_substitution s (!ctxt);
	      (* and continue *)
	      0, args, ty'
	    | _ -> 
	      raise (DoudouException (FreeError "typeinfer on App: case not supported, the function type is neither a (->) or a free variable"))
	) in
	(* before returning we need to repush the (new) type *)
	push_terms ctxt [ty];
	(* and returns the information *)
	remaining_args, nb_processed_args + added
      ) 0 args in
      (* we pop the ty *)
      let [ty] = pop_terms ctxt 1 in
      (* then we pop the arguments *)
      let args = List.rev (map_nth (fun i ->
	let [arg] = pop_terms ctxt 1 in
	let n = pop_nature ctxt in
	(arg, n)
      ) nb_args) in
      (* finally we pop the application head *)
      let [te] = pop_terms ctxt 1 in
      App (te, args, pos), ty
    
    (* for the AVar we introduce a free var of type, and a free var of this type *)
    | AVar pos -> 
      let fvty = add_fvar ctxt (Type nopos) in
      let fvte = add_fvar ctxt (TVar (fvty, nopos)) in
      TVar (fvte, pos), TVar (fvty, nopos)

    (* destruction *)
    | Match (te, eqs, pos) -> (
      (* first we typecheck the term to destruct *)
      let te, ty = typeinfer defs ctxt te in 
      (*printf "|- %s :: %s\n" (term2string !ctxt te) (term2string !ctxt ty);*)
      (* here we should verify it is an inductive *)
      (* we create a free variable for the returning types of the destruction *)
      let fvty = add_fvar ctxt (Type nopos) in
      let fvte = add_fvar ctxt (TVar (fvty, nopos)) in      
      (* then we typecheck equation by equations *)
      let eqs = List.map (fun (lhs, rhs) ->
	(* we infer the pattern *)
	let lhs', lhste, lhsty = typeinfer_pattern defs ctxt lhs in
	(* we compare the pattern types, and the term types *)
	let _ = unification_term_term defs ctxt (shift_term ty (pattern_size lhs)) lhsty in
	(* close the value alias for pattern quantified variables *)
	close_context ctxt;  
	(* and we typecheck the rhs *)
	let rhs, rhsty = typecheck defs ctxt rhs (TVar (fvte, nopos)) in
	(* we pop all the quantifications *)
	let _ = pop_quantifications ctxt [] (pattern_size lhs') in
	(* returns the equation *)
	lhs', rhs
      ) eqs in
      (* and we returns the typed term, and the value of the free variable precedently created to bear the whole match type *)
      Match (te, eqs, pos), fvar_value !ctxt fvte
    )

  ) with
    | DoudouException ((CannotInfer _) as err) ->
      raise (DoudouException err)
    | DoudouException err ->
      ctxt := saved_ctxt;
      raise (DoudouException (CannotInfer (!ctxt, te, err)))
  ) in 
  if !debug then printf "typeinfer result : %s :: %s\n" (term2string !ctxt (fst res)) (term2string !ctxt (snd res));
  res
and typecheck_pattern (defs: defs) (ctxt: context ref) (p: pattern) (ty: term) : pattern * term * term =
  let p', pte, pty = typeinfer_pattern defs ctxt p in
  
  let ty' = shift_term ty (pattern_size p') in

  (* we try to detect if there is more implicite quantification in the infer type than the typechecked type *)
  if nb_implicit_arguments defs ctxt pty > nb_implicit_arguments defs ctxt ty then (
    (* we need to add enough implicit arguments *)
    let new_args = List.map (fun (s, _, _, _) -> PVar (symbol2string s, AVar nopos, nopos), Implicit) (take (nb_implicit_arguments defs ctxt pty - nb_implicit_arguments defs ctxt ty) (fst (destruct_impl pty))) in
    let p'' = match p with | PCste (s, spos) -> PApp ((s, spos), new_args, AVar nopos, nopos) in
    ctxt := drop (pattern_size p') !ctxt;
    typecheck_pattern defs ctxt p'' ty
  ) else (
    push_terms ctxt [pte];
    let ty = unification_term_term defs ctxt ty' pty in
    let [pte] = pop_terms ctxt 1 in
    p', pte, ty  
  )

and typeinfer_pattern (defs: defs) (ctxt: context ref) (p: pattern) : pattern * term * term =
  match p with
    | PApp ((s, spos), args, ty, pos) -> (
      let sty = constante_type defs s in
      let (appty, te_done, args_done) = fold_cont (fun (appty, te_done, args_done) args ->

	let appty = (
	  match appty with
	    | Impl _ -> appty
	    | _ -> reduction defs ctxt unification_strat appty
	) in

	match args, appty with
	  | (arg, n1)::tl, Impl ((_, ty, n2, _), _, _) when n1 = n2 ->	    	    

	    (* we typecheck the pattern *)
	    let (arg, argte, argty) = typecheck_pattern defs ctxt arg ty in
	    (* we compute the type after application of the term *)
	    let Impl ((_, _, _, _), te, _) = shift_term appty (pattern_size arg) in
	    let appty = term_substitution (context2substitution !ctxt) (shift_term (term_substitution (IndexMap.singleton 0 (shift_term argte 1)) te) (-1)) in
	    (* we compute the te_done at this level *)
	    let te_done = List.map (fun (te, n) -> term_substitution (context2substitution !ctxt) (shift_term te (pattern_size arg)), n) te_done in
	    tl, (appty, te_done @ [argte, n1], args_done @ [arg, n1])	
	  | (arg, Explicit)::tl, Impl ((s, _, Implicit, _), _, _) ->
	    (* we just add an implicit *)
	    (PVar (symbol2string s, AVar nopos, spos), Implicit)::args, (appty, te_done, args_done)
	  | _ ->
	    raise (DoudouException (FreeError "bad case"))
      ) (sty, [], []) args in

      let p = PApp ((s, spos), args_done, appty, pos) in

      let ty, _ = typecheck defs ctxt ty (Type nopos) in
      let appty = unification_term_term defs ctxt appty ty in

      p, App (Cste (s, spos), te_done, pos), appty
      
    )
    | PVar (n, ty, p) ->
      let fvty = add_fvar ctxt (Type nopos) in
      let fvte = add_fvar ctxt (TVar (fvty, nopos)) in
      ctxt := build_new_frame (Name n) ~value:(TVar (fvte, p)) (TVar (fvty, nopos)) :: !ctxt;      
      let ty, _ = typecheck defs ctxt ty (Type nopos) in 
      let ty = unification_term_term defs ctxt ty (TVar (fvty, nopos)) in
      PVar (n, ty, p), TVar (0, p), ty

    | PCste (s, p) ->
      PCste (s, p), Cste (s, p), constante_type defs s

    | PType p->
      PType p, Type p, Type nopos

    | PAVar (ty, p) ->
      let fvty = add_fvar ctxt (Type nopos) in
      let fvte = add_fvar ctxt (TVar (fvty, nopos)) in
      ctxt := build_new_frame (Symbol ("_", Nofix)) ~value:(TVar (fvte, p)) (TVar (fvty, nopos)) :: !ctxt;      
      let ty, _ = typecheck defs ctxt ty (Type nopos) in 
      let ty = unification_term_term defs ctxt ty (TVar (fvty, nopos)) in
      PAVar (ty, p), TVar (0, p), ty

    | PAlias (s, p, ty, pos) ->
      let p, pte, pty = typeinfer_pattern defs ctxt p in
      let pte = shift_term pte 1 in
      let pty = shift_term pty 1 in
      ctxt := build_new_frame (Name s) ~value:pte pty :: !ctxt;
      let ty, _ = typecheck defs ctxt ty (Type nopos) in 
      let ty = unification_term_term defs ctxt ty pty in
      PAlias (s, p, ty, pos), TVar (0, pos), ty


(* typechecking for destructors where type of l.h.s := type of r.h.s *)
and typecheck_equation (defs: defs) (ctxt: context ref) (lhs: pattern) (rhs: term) : pattern * term =
  (* we infer the pattern *)
  let lhs', lhste, lhsty = typeinfer_pattern defs ctxt lhs in
  (* close the value alias for pattern quantified variables *)
  close_context ctxt;  
  (* and we typecheck the rhs *)
  let rhs, rhsty = typecheck defs ctxt rhs lhsty in
  let _ = pop_quantifications ctxt [] (pattern_size lhs') in
  (*ctxt := drop (pattern_size lhs') !ctxt;*)
  lhs', rhs

(* close a context with bvar valued to fvars *)
and close_context (ctxt: context ref) : unit =
  let s = List.fold_left (fun s frame ->
    let s = shift_substitution s 1 in
    match frame.value with
      | TVar (i, p) when i < 0 && not (IndexMap.mem i s) -> IndexMap.add i (TVar (0, p)) s
      | _ -> s

  ) IndexMap.empty (List.rev !ctxt) in
  ctxt := context_substitution s !ctxt

(* a simple equality: basically we try to unify to term, and look for the empty substitution *)
and equality_term_term (defs: defs) (ctxt: context ref) (te1: term) (te2: term) : bool =
  try
    let ctxt' = ref !ctxt in
    let _ = unification_term_term defs ctxt' te1 te2 in
    (* here we can use structural equality, because it is exactly what we want *)
    IndexMap.compare compare (context2substitution !ctxt) (context2substitution !ctxt') = 0
  with
    | _ -> false
(* a term rewriting based on unification
   
 *)
and rewrite_term (defs: defs) (ctxt: context) (lhs: term) (rhs: term) (te: term) : term =
  (* the base case:
     - we push rhs in the term stack
     - we try to unify lhs and te 
     - if it works the free variable in rhs will be substituted so that we pop rhs and return it     
  *)
  try 
    let ctxt' = ref ctxt in
    push_terms ctxt' [rhs];
    let _ = unification_term_term defs ctxt' lhs te in
    let [rhs] = pop_terms ctxt' 1 in
    rhs
  with
    (* if unification fails we will try on sub terms *)
    | DoudouException (UnknownUnification _) | DoudouException (NoUnification _) ->
      match te with
	(* for all cases without subterms, we simply returns the original term *)
	| Type _ | Cste _ | Obj _ | TVar _ | AVar _ | TName _ -> te
	(* for app we just apply the rewriting to the head and the arguments *)	  
	| App (f, args, pos) ->
	  App (rewrite_term defs ctxt lhs rhs f,
	       List.map (fun (arg, n) -> rewrite_term defs ctxt lhs rhs arg, n) args,
	       pos)
	(* for the quantifications, 
	   we rewrite the type in the quantification, 
	   push a frame/shift the rewriting elements,
	   and rewrite the body
	*)
	| Impl ((s, ty, n, p) as q, body, p') ->
	  Impl ((s, rewrite_term defs ctxt lhs rhs ty, n, p),
		(let ctxt' = ref ctxt in
		 push_quantification q ctxt';
		 let ctxt' = !ctxt' in
		 let lhs' = shift_term lhs 1 in
		 let rhs' = shift_term rhs 1 in
		 rewrite_term defs ctxt' lhs' rhs' body),
		p'
	  )
	| Lambda ((s, ty, n, p) as q, body, p') ->
	  Lambda ((s, rewrite_term defs ctxt lhs rhs ty, n, p),
		  (let ctxt' = ref ctxt in
		   push_quantification q ctxt';
		   let ctxt' = !ctxt' in
		   let lhs' = shift_term lhs 1 in
		   let rhs' = shift_term rhs 1 in
		   rewrite_term defs ctxt' lhs' rhs' body),
		  p'
	  )
		  
