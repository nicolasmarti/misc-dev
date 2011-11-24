open Def
open Misc

(*************************************)
(*      substitution/rewriting       *)
(*************************************)

(* substitution = replace variables (free or bound) by terms (used for typechecking/inference with free variables, and for reduction with bound variable) *)

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

(* substitution *)
let rec term_substitution (s: substitution) (te: term) : term =
  match te with
    | Type _ | Cste _ | Obj _ -> te
    | TVar (i, _) as v -> 
      (
	try 
	  IndexMap.find i s 
	with
	  | Not_found -> v
      )
    | AVar _ -> raise (DoudouException (FreeError "term_substitution catastrophic: AVar"))
    | TName _ -> raise (DoudouException (FreeError "term_substitution catastrophic: TName"))
    | App (te, args, pos) ->
      App (term_substitution s te,
	   List.map (fun (te, n) -> term_substitution s te, n) args,
	   pos)
    | Impl ((symb, ty, n, p), te, pos) ->
      Impl ((symb, term_substitution s ty, n, p),
	    term_substitution (shift_substitution s 1) te,
	    pos)
    | Lambda ((symb, ty, n, p), te, pos) ->
      Lambda ((symb, term_substitution s ty, n, p),
	      term_substitution (shift_substitution s 1) te,
	      pos)
    | Match (te, eqs, p) ->
      Match (term_substitution s te,
	     List.map (fun eq -> eq_substitution s eq) eqs,
	     p
      )

and pattern_substitution (s: substitution) (p: pattern) : pattern =
  match p with
    | PType _ | PCste _ -> p
    | PVar (n, ty, pos) -> PVar (n, term_substitution s ty, pos)
    | PAlias (n, p, ty, pos) -> PAlias (n, pattern_substitution s p, term_substitution (shift_substitution s (pattern_size p)) ty, pos)
    | PApp (symb, args, ty, pos) ->
      PApp (symb,
	    fst (
	      List.fold_left (fun (args, s) (p, n) ->
		args @ [pattern_substitution s p, n], shift_substitution s (pattern_size p)
	      ) ([], s) args
	    ),
	    term_substitution (shift_substitution s (pattern_size p)) ty,
	    pos)

and eq_substitution (s: substitution) (eq: equation) : equation =
  let p, te = eq in
  pattern_substitution s p, term_substitution (shift_substitution s (pattern_size p)) te

(* shift vars index in a substitution 
   only bound variable of the l.h.s. of the map are shifted too
*)
and shift_substitution (s: substitution) (delta: int) : substitution =
  IndexMap.fold (fun key value acc -> 
    try 
      if key < 0 then 
	IndexMap.add key (shift_term value delta) acc
      else 
	if key + delta < 0 then acc else IndexMap.add (key + delta) (shift_term value delta) acc 
    with
      | DoudouException (Unshiftable_term _) -> acc
  ) s IndexMap.empty
      
(* shift bvar index in a term *)
and shift_term (te: term) (delta: int) : term =
  leveled_shift_term te 0 delta

(* shift bvar index in a term, above a given index *)
and leveled_shift_term (te: term) (level: int) (delta: int) : term =
  match te with
    | Type _ | Cste _ | Obj _ | AVar _ | TName _ -> te
    | TVar (i, _) when i < 0 -> te
    | TVar (i, pos) as v when i >= 0 ->
      if i >= level then
	if i + delta < level then (
	  raise (DoudouException (Unshiftable_term (te, level, delta)))
	)
	else
	  TVar (i + delta, pos)
      else
	v

    | App (te, args, pos) ->
      App (
	leveled_shift_term te level delta,
	List.map (fun (te, n) -> leveled_shift_term te level delta, n) args,
	pos
      )
    | Impl ((s, ty, n, p), te, pos) ->
      Impl ((s, leveled_shift_term ty level delta, n, p), leveled_shift_term te (level + 1) delta,
	    pos)

    | Lambda ((s, ty, n, p), te, pos) ->
      Lambda ((s, leveled_shift_term ty level delta, n, p), leveled_shift_term te (level + 1) delta, pos)

    | Match (te, eqs, pos) ->
      Match (leveled_shift_term te level delta,
	     List.map (fun eq -> leveled_shift_equation eq level delta) eqs,
	     pos)

and leveled_shift_pattern (p: pattern) (level: int) (delta: int) : pattern =
  match p with
    | PType _ | PCste _ -> p
    | PVar (n, ty, pos) -> PVar (n, leveled_shift_term ty level delta, pos)
    | PAVar (ty, pos) -> PAVar (leveled_shift_term ty level delta, pos)
    | PAlias (s, p, ty, pos) -> PAlias (s, leveled_shift_pattern p level delta, leveled_shift_term ty (level + pattern_size p) delta, pos)
    | PApp (s, args, ty, pos) ->
      PApp (s,
	    fst (
	      List.fold_left (fun (args, level) (p, n) ->
		args @ [leveled_shift_pattern p level delta, n], level + pattern_size p
	      ) ([], level) args
	    ),
	    leveled_shift_term ty (level + pattern_size p) delta, pos)

and leveled_shift_equation (eq: equation) (level: int) (delta: int) : equation =
  let p, te = eq in
  leveled_shift_pattern p level delta, leveled_shift_term te (level + pattern_size p) delta
