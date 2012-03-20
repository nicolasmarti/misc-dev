open Def
open Misc
open Substitution
open Extlist
open Libparser
open Printf

(* push the bvars of a pattern in a context *)
let push_pattern_bvars (ctxt: context) (l: (name * term * term) list) : context =
  List.fold_left (fun ctxt (n, ty, v) ->
    (
      build_new_frame (Name n) ~value:v ty
    ) :: ctxt	     

  ) ctxt l


(* returns the list of bound variables, their value (w.r.t. other bound variable) and their type in a pattern    
   it also returns the overall value of the pattern (under the pattern itself)
   hd::tl -> hd is the "oldest" variable, and is next to be framed
*)

let rec pattern_bvars (p: pattern) : (name * term * term) list * term =
  match p with
    | PType pos -> [], Type pos
    | PVar (n, ty, pos) -> [n, ty, TVar (0, pos)], TVar (0, pos)
    | PAVar (ty, pos) -> ["_", ty, TVar (0, pos)], TVar (0, pos)
    | PCste (s, pos) -> [] , Cste (s, pos)
    | PAlias (n, p, ty, pos) -> 
      let l, te = pattern_bvars p in
      (* the value is shift by one (under the alias-introduced var) *)
      let te = shift_term te 1 in
	(l @ [n, ty, te], TVar (0, pos))
    | PApp ((s, p), args, ty, pos) -> 
      let (delta, l, rev_values) = 
	(* for sake of optimization the value list is in reverse order *)
	List.fold_left (fun (delta, l, rev_values) (p, n) ->
	  (* first we grab the result for p *)
	  let (pl, te) = pattern_bvars p in
	  (* then we need to shift the value term by the current delta level *)
	  let te = shift_term te delta in
	  (* we update the delta value, and returns the concatenation *)
	  (delta + List.length l, l @ pl, (te, n)::rev_values)
	) (0, [], []) args in
      (l, App (Cste (s, p), List.rev rev_values, pos))


(* compute the context under a pattern *)
let input_pattern (ctxt: context) (p: pattern) : context =
  (* we extract the list of bound variable in the pattern *)
  let (bvars, _) = pattern_bvars p in
  (* we build a new context with the pattern bvars frames pushed *)
  push_pattern_bvars ctxt bvars

(* apply a substitution in a context *)
let context_substitution (s: substitution) (ctxt: context) : context =
  fst (mapacc (fun s frame ->
    { frame with
      ty = term_substitution s frame.ty;
      value = term_substitution s frame.value;
      fvs = List.map (fun (index, ty, value) -> index, term_substitution s ty, term_substitution s value) frame.fvs;
      termstack = List.map (term_substitution s) frame.termstack;
      patternstack = List.map (pattern_substitution s) frame.patternstack
    }, shift_substitution s (-1)
  ) s ctxt
  )

(* retrieve the debruijn index of a bound var through its symbol *)
let bvar_lookup (ctxt: context) (s: symbol) : index option =
  let res = fold_stop (fun level frame ->
    if symbol2string frame.symbol = symbol2string s then
      Right level
    else
      Left (level + 1)
  ) 0 ctxt in
  match res with
    | Left _ -> None
    | Right level -> Some level

(* grab the value of a bound var *)
let bvar_value (ctxt: context) (i: index) : term =
  try (
    let frame = List.nth ctxt i in
    let value = frame.value in
    shift_term value i
  ) with
    | Failure "nth" -> raise (DoudouException (UnknownBVar (i, ctxt)))
    | Invalid_argument "List.nth" -> raise (DoudouException (NegativeIndexBVar i))

(* grab the type of a bound var *)
let bvar_type (ctxt: context) (i: index) : term =
  try (
    let frame = List.nth ctxt i in
    let ty = frame.ty in
    shift_term ty i
  ) with
    | Failure "nth" -> raise (DoudouException (UnknownBVar (i, ctxt)))
    | Invalid_argument "List.nth" -> raise (DoudouException (NegativeIndexBVar i))

(* grab the value of a free var *)
let fvar_value (ctxt: context) (i: index) : term =
  let lookup = fold_stop (fun level frame ->
    let lookup = fold_stop (fun () (index, ty, value) -> 
      if index = i then Right value else Left ()
    ) () frame.fvs in
    match lookup with
      | Left () -> Left (level + 1)
      | Right res -> Right (shift_term res level)
  ) 0 ctxt in
  match lookup with
    | Left _ -> raise (DoudouException (UnknownFVar (i, ctxt)))
    | Right res -> res

(* grab the type of a free var *)
let fvar_type (ctxt: context) (i: index) : term =
  let lookup = fold_stop (fun level frame ->
    let lookup = fold_stop (fun () (index, ty, value) -> 
      if index = i then Right ty else Left ()
    ) () frame.fvs in
    match lookup with
      | Left () -> Left (level + 1)
      | Right res -> Right (shift_term res level)
  ) 0 ctxt in
  match lookup with
    | Left _ -> raise (DoudouException (UnknownFVar (i, ctxt)))
    | Right res -> res

(* extract a substitution from the context *)
let context2substitution (ctxt: context) : substitution =
  fst (List.fold_left (
    fun (s, level) frame -> 
      let s = List.fold_left (fun s (index, ty, value) ->
	IndexMap.add index (shift_term value level) s
      ) s frame.fvs in
      (s, level+1)
  ) (IndexMap.empty, 0) ctxt
  )

(* pushing and poping terms in the term stack 
   N.B.: with side effect
*)
let push_terms (ctxt: context ref) (tes: term list) : unit =
  let (hd::tl) = !ctxt in
  ctxt := ({hd with termstack = tes @ hd.termstack})::tl

let pop_terms (ctxt: context ref) (sz: int) : term list =
  let (hd::tl) = !ctxt in  
  ctxt := ({hd with termstack = drop sz hd.termstack})::tl;
  take sz hd.termstack

(* pushing and poping natures in the nature stack 
   N.B.: with side effect
*)
let push_nature (ctxt: context ref) (n: nature) : unit =
  let (hd::tl) = !ctxt in
  ctxt := ({hd with naturestack = n :: hd.naturestack})::tl

let pop_nature (ctxt: context ref) : nature =
    let (hd::tl) = !ctxt in  
    ctxt := ({hd with naturestack = List.tl hd.naturestack})::tl;
    List.hd hd.naturestack

(* unfold a constante *)
let unfold_constante (defs: defs) (s: symbol) : value =
  try 
    (fun (_, _, value) -> value) (Hashtbl.find defs.store (symbol2string s))
  with
    | Not_found -> raise (DoudouException (UnknownCste s))

(* grab the type of a constante *)
let constante_type (defs: defs) (s: symbol) : term =
  try 
    (fun (_, ty, _) -> ty) (Hashtbl.find defs.store (symbol2string s))
  with
    | Not_found -> raise (DoudouException (UnknownCste s))

(* grab the real symbol of a constante *)
let constante_symbol (defs: defs) (s: symbol) : symbol =
  try 
    (fun (s, _, _) -> s) (Hashtbl.find defs.store (symbol2string s))
  with
    | Not_found -> raise (DoudouException (UnknownCste s))

(* pop a frame *)
let pop_frame (ctxt: context) : context * frame =
  match List.hd ctxt with
    | { fvs = []; termstack = []; naturestack = []; patternstack = []; _} ->
      List.tl ctxt, List.hd ctxt
    | { fvs = _::_; termstack = []; naturestack = []; patternstack = []; _} ->
      raise (DoudouException (FreeError "Case not yet supported, pop_frame with still fvs"))
    | _ -> raise (DoudouException (PoppingNonEmptyFrame (List.hd ctxt)))

(* poping frame: fst := resulting context, snd := poped frames *)
let rec pop_frames (ctxt: context) (nb: int) : context * context =
  if nb <= 0 then ctxt, [] else 
    let ctxt, frame = pop_frame ctxt in 
    let ctxt, frames = pop_frames ctxt (nb - 1) in
    ctxt, frame::frames

(* we add a free variable *)
let add_fvar (ctxt: context ref) (ty: term) : int =
  let next_fvar_index = 
    match (fold_stop (fun acc frame ->
      match frame.fvs with
	| [] -> Left acc
	| (i, _, _)::_ -> Right (i - 1)
    ) (-1) !ctxt)
    with
      | Left i -> i
      | Right i -> i
  in
  let frame = List.hd !ctxt in
  ctxt := ({ frame with fvs = (next_fvar_index, ty, TVar (next_fvar_index, nopos))::frame.fvs})::List.tl !ctxt;
  next_fvar_index

(* add definitions to a defs *)

let addAxiom (defs: defs ref) (s: symbol) (ty: term) : unit =
  (* just checking that there is no redefinition *)
  if Hashtbl.mem !defs.store (symbol2string s) then raise (DoudouException (FreeError (String.concat "" ["redefinition of symbol: "; (symbol2string s)])));

  (* update the definitions *)
  Hashtbl.replace !defs.store (symbol2string s) (s, ty, Axiom);
  defs := {!defs with hist = [s]::!defs.hist }

let addEquation (defs: defs ref) (s: symbol) (eq: equation) : unit =
  (* just checking that there is a definition *)
  if not (Hashtbl.mem !defs.store (symbol2string s)) then raise (DoudouException (FreeError (String.concat "" ["symbol: "; (symbol2string s); " is not defined!"])));

  (* we verify that it is either an equation or an axioms*)
  let eqs = (match unfold_constante !defs s with
    | Axiom -> []
    | Equation eqs -> eqs
    | Inductive _ -> raise (DoudouException (FreeError (String.concat "" ["symbol: "; (symbol2string s); " is an Inductive Type!"])))
    | Constructor -> raise (DoudouException (FreeError (String.concat "" ["symbol: "; (symbol2string s); " is a constructor!"])))
  ) in
  (* update the definitions *)
  let ty = constante_type !defs s in
  Hashtbl.replace !defs.store (symbol2string s) (s, ty, Equation (eqs @ [eq]));
  defs := {!defs with hist = [s]::!defs.hist }

let addInductive (defs: defs ref) (s: symbol) (ty: term) (constrs: (symbol * term) list) : unit =
  (* just checking that there is no redefinition for the type *)
  if Hashtbl.mem !defs.store (symbol2string s) then raise (DoudouException (FreeError (String.concat "" ["redefinition of symbol: "; (symbol2string s)])));
  let _ = List.map (fun (s, _) -> if Hashtbl.mem !defs.store (symbol2string s) then raise (DoudouException (FreeError (String.concat "" ["redefinition of symbol: "; (symbol2string s)])))) constrs in

  (* update the definitions *)
  Hashtbl.replace !defs.store (symbol2string s) (s, ty, Inductive (List.map fst constrs));
  let _ = List.map (fun (s, ty) -> Hashtbl.replace !defs.store (symbol2string s) (s, ty, Constructor)) constrs in
  defs := {!defs with hist = (s::(List.map fst constrs))::!defs.hist }

(* remove back a set of definitions *)
let undoDefinition (defs: defs ref) : symbol list =
  match !defs.hist with
    | [] -> []
    | hd::tl ->
      let l = List.map (fun s ->
	match unfold_constante !defs s with
	  | Equation eqs when List.length eqs > 0 -> 
	    let ty = constante_type !defs s in
	    Hashtbl.replace !defs.store (symbol2string s) (s, ty, Equation (take (List.length eqs - 1) eqs));
	    []
	  | _ -> 
	    Hashtbl.remove !defs.store (symbol2string s);
	    [s]
      ) (List.rev hd) in
      defs := {!defs with hist = tl};
      List.flatten l

(* this function rewrite all free vars that have a real value in the upper frame of a context into a list of terms, and removes them *)
let rec flush_fvars (defs: defs) (ctxt: context ref) (l: term list) : term list =
  (*if !debug then printf "before flush_vars: %s\n" (context2string !ctxt);*)
  let hd, tl = List.hd !ctxt, List.tl !ctxt in
  (* we compute the fvars of the terms *)
  let lfvs = List.fold_left (fun acc te -> IndexSet.union acc (fv_term te)) IndexSet.empty l in
  (* and traverse the free variables *)
  let (terms, fvs) = fold_cont (fun (terms, fvs) ((i, ty, te)::tl) ->
    match te with
      | TVar (i', _) when not (IndexSet.mem i' lfvs) ->
	(* there is no value for this free variable, and it does not appear in the terms --> remove it *)
	tl, (terms, fvs)
      | TVar (i', _) when IndexSet.mem i' lfvs ->
	(* there is no value for this free variable, but it does appear in the terms --> keep it *)
	tl, (terms, fvs @ [i, ty, te])
      | _ -> 
      (* there is a value, we can get rid of the free var *)
	(*if !debug then printf "flush_vars, rewrite %s --> %s\n" (term2string !ctxt (TVar (i, nopos))) (term2string !ctxt te);*)
	let s = (IndexMap.singleton i te) in
	let terms = List.map (fun hd -> term_substitution s hd) terms in
	let tl = List.map (fun (i, ty, te) -> i, term_substitution s ty, term_substitution s te) tl in
	tl, (terms, fvs)
  ) (l, []) (List.rev hd.fvs) in
  (* here we are removing the free vars and putting them bellow only if they have no TVar 0 in their term/type *)
  (* first we shift them *)
  let terms, fvs = List.fold_left (fun (terms, acc) (i, ty, te) ->
    try 
      terms, (acc @ [i, shift_term ty (-1), shift_term te (-1)])
    with
      | DoudouException (Unshiftable_term _) ->
	(* we have a free variable that has a type / value containing the symbol in hd -> 
	   we try to ask an oracle if it can guess the term
	*)
	if !debug_oracles then printf "flush_fvars asks to oracles: %s\n" (!term2string_ptr !ctxt ty);
	let _(*guessed_value*) = fold_stop (fun () oracle ->
	  match oracle (defs, !ctxt, ty) with
	    | None -> Left ()
	    | Some prf ->
		(* we check the proof *)
	      try 
		let _ = !typecheck_ptr defs ctxt prf ty in
		if not (IndexSet.mem i (fv_term te)) then Right prf else Left ()
	      with
		| _ -> 		  
		  Left ()
	) () !oracles_list in
	raise (DoudouException (FreeError "we failed to infer a free variable that cannot be out-scoped"))
  ) (terms, []) (List.rev fvs) in
  (match tl with
    (* we are in toplevel, we return an error if there is still free variables *)
    | [] -> 
      if List.length fvs = 0 then
	ctxt := ({hd with fvs = []})::tl
      else
	raise (DoudouException (FreeError "flush_fvars failed because the term still have freevariables"))
    (* we are not in toplevel -> we copy the fvs (that have been shifted), to the previous level *)
    | hd'::tl -> ctxt := ({hd with fvs = []})::({hd' with fvs = fvs @ hd'.fvs})::tl
  ); 
  (*if !debug then printf "after flush_vars: %s\n" (context2string !ctxt);*)
  terms

(* pushing / poping of quantifications *)
let push_quantification (q : symbol * term * nature * pos) (ctxt: context ref) : unit =
  let s, ty, n, p = q in
  (* we build a frame (shifting the type) *)
  let new_frame = build_new_frame s ~nature:n ~pos:p (shift_term ty 1) in
  ctxt := new_frame::!ctxt

let pop_quantification (defs: defs) (ctxt: context ref) (tes: term list) : (symbol * term * nature * pos) * term list =
  (* we flush the free variables *)
  let tes = flush_fvars defs ctxt tes in
  (* we grab the remaining context and the popped frame *)
  let ctxt', frame = pop_frame (!ctxt) in
  (* we set the context *)
  ctxt := ctxt';
  (* and returns the quantifier *)
  (frame.symbol, shift_term frame.ty (-1), frame.nature, frame.pos), tes  

let rec pop_quantifications (defs: defs) (ctxt: context ref) (tes: term list) (n: int) : (symbol * term * nature * pos) list * term list =
  match n with
    | _ when n < 0 -> raise (DoudouException (FreeError "Catastrophic: negative n in pop_quantifications"))
    | 0 -> [], tes
    | _ ->
      let hd, tes = pop_quantification defs ctxt tes in
      let tl, tes = pop_quantifications defs ctxt tes (n-1) in
      hd::tl, tes
