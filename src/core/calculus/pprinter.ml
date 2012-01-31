open Def
open Misc
open Libpprinter
open Libparser
open Extlist
open Substitution
open Context
open Primitive

let rec withParen (t: token) : token =
  Box [Verbatim "("; t; Verbatim ")"]

let rec withBracket (t: token) : token =
  Box [Verbatim "{"; t; Verbatim "}"]

(* a data structure to mark the place where the term/pattern is *)
type place = InNotation of op * int (* in the sndth place of the application to the notation with op *)
	     | InApp (* in the head of application *)
	     | InArg of nature (* as an argument (Explicit) *)
	     | InAlias  (* in an alias pattern *)
	     | Alone (* standalone *)

(* TODO: add options for 
   - printing implicit terms 
   - printing type annotation
   - source info
*)

type pp_option = {
  show_implicit : bool;
  show_indices : bool;
  show_position : bool;
}

let pp_option = ref {show_implicit = false; show_indices = false; show_position = false}

(* transform a term into a box *)
let rec term2token (ctxt: context) (te: term) (p: place): token =
  match te with
    | Type _ -> Verbatim "Type"
    | Cste (s, _) -> Verbatim (symbol2string s)
    | Obj (o, _) -> o#pprint ()
    | TVar (i, _) when i >= 0 -> 
      let frame = get_bvar_frame ctxt i in
      if !pp_option.show_indices then
	Box [Verbatim (symbol2string (frame.symbol)); Verbatim "["; Verbatim (string_of_int i); Verbatim "]"]
      else
	Verbatim (symbol2string (frame.symbol))
    | TVar (i, _) when i < 0 -> 
      Verbatim (String.concat "" ["?["; string_of_int i;"]"])

    (* we need to split App depending on the head *)
    (* the case for notation Infix *)
    | App (Cste (Symbol (s, Infix (myprio, myassoc)), _), args, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 2->
      (* we should put parenthesis in the following condition: *)
      (match p with
	(* if we are an argument *)
	| InArg Explicit -> withParen
	(* if we are in a notation such that *)
	(* a prefix or postfix binding more  than us *)
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	(* or another infix with higher priority *)
	| InNotation (Infix (i, _), _) when i > myprio -> withParen
	(* or another infix with same priority depending on the associativity and position *)
	(* I am the second argument and its left associative *)
	| InNotation (Infix (i, LeftAssoc), 2) when i = myprio -> withParen
	(* I am the first argument and its right associative *)
	| InNotation (Infix (i, RightAssoc), 1) when i = myprio -> withParen

	(* else we do not need parenthesis *)
	| _ -> fun x -> x
      )	(
	match (if !pp_option.show_implicit then List.map fst args else filter_explicit args) with
	  | arg1::arg2::[] ->
	    let arg1 = term2token ctxt arg1 (InNotation (Infix (myprio, myassoc), 1)) in
	    let arg2 = term2token ctxt arg2 (InNotation (Infix (myprio, myassoc), 2)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg1; te; arg2])
	  | _ -> raise (DoudouException (FreeError "term2token, App infix case: irrefutable patten"))
       )
    (* the case for Prefix *)
    | App (Cste (Symbol (s, (Prefix myprio)), _), args, _) when not !pp_option.show_implicit &&List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a postfix notation more binding than us
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	| _ -> fun x -> x
      ) (
	match filter_explicit args with
	  | arg::[] ->
	    let arg = term2token ctxt arg (InNotation (Prefix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [te; arg])
	  | _ -> raise (DoudouException (FreeError "term2token, App prefix case: irrefutable patten"))
       )

    (* the case for Postfix *)
    | App (Cste (Symbol (s, (Postfix myprio)), _), args, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a prefix notation more binding than us
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| _ -> fun x -> x
      ) (
	match filter_explicit args with
	  | arg::[] ->
	    let arg = term2token ctxt arg (InNotation (Postfix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg; te])
	  | _ -> raise (DoudouException (FreeError "term2token, App postfix case: irrefutable patten"))
       )

    (* if we have only implicit argument (and if we don't want to print them, then we are not really considered as a App  *)
    | App (te, args, _) when not !pp_option.show_implicit && List.length (filter_explicit args) = 0 ->
      term2token ctxt te p

    (* general case *)
    | App (te, args, _) ->
      (* we only embed in parenthesis if
	 - we are an argument of an application
      *)
      (match p with
	| InArg Explicit -> withParen
	| _ -> fun x -> x
      ) (
	let args = List.map (fun te -> term2token ctxt te (InArg Explicit)) (if !pp_option.show_implicit then List.map fst args else filter_explicit args) in
	let te = term2token ctxt te InApp in
	Box (intercalate (Space 1) (te::args))
       )

    (* implication *)
    | Impl ((s, ty, nature, _), te, _) ->
      (* we embed in parenthesis if 
	 - embed as some arg 
	 - ??
      *)
      (
	match p with
	  | InArg Explicit -> withParen
	  | _ -> fun x -> x
      )
	(
	  (* the lhs of the ->*)
	  let s', lhs = 
	    (* if the symbol is Nofix _ -> we skip the symbol *)
	    (* IMPORTANT: it means that Symbol ("_", Nofix)  as a special meaning !!!! *)
	    match s with
	      | Symbol ("_", Nofix) | _ when not (IndexSet.mem 0 (bv_term te))->
		(* we only put brackets if implicit *)
		Symbol ("_", Nofix), (if nature = Implicit then withBracket else fun x -> x) (term2token ctxt ty (InArg nature))
	      | Name _ -> 
		(* here we put the nature marker *)
		let s = Name (fresh_name_context ~basename:(symbol2string s) ctxt) in
		s, (if nature = Implicit then withBracket else withParen)
		  (Box [Verbatim (symbol2string s); Space 1; Verbatim "::"; Space 1; term2token ctxt ty Alone])
	      | _ -> s, (if nature = Implicit then withBracket else withParen)
		(Box [Verbatim (symbol2string s); Space 1; Verbatim "::"; Space 1; term2token ctxt ty Alone])
	  in 
	  (* for computing the r.h.s, we need to push a new frame *)
	  let newframe = build_new_frame s' (shift_term ty 1) in
	  let rhs = term2token (newframe::ctxt) te Alone in
	  Box [lhs; Space 1; Verbatim "->"; Space 1; rhs]
	)

    (* quantification *)
    | Lambda ((s, ty, nature, _), _, _) ->
      (* we embed in parenthesis if 
	 - embed as some arg 
	 - ??
      *)
      (
	match p with
	  | InArg Explicit -> withParen
	  | _ -> fun x -> x
      )
	(	  
	  (* the lhs of the \\ *)
	  let lhs, rhs = destruct_lambda te in
	  let ctxt, lhs = 
	    fold_cont (fun (ctxt, acc) ((s, ty, n, p)::tl) ->
	      let s = 
		match s with
		  | _ when not (IndexSet.mem 0 (bv_term (construct_lambda tl rhs))) -> Symbol ("_", Nofix)
		  | Symbol ("_", Nofix) when IndexSet.mem 0 (bv_term (construct_lambda tl rhs)) -> Name (fresh_name_context ctxt)
		  | Name _ -> Name (fresh_name_context ~basename:(symbol2string s) ctxt)
		  | _ -> s in
	      tl, ((build_new_frame s (shift_term ty 1))::ctxt,
		   acc @ 
		     [Space 1; (if n = Implicit then withBracket else withParen) (Box [Verbatim (symbol2string s); Space 1; Verbatim "::"; Space 1; term2token ctxt ty Alone])]
	      )
	    ) (ctxt, []) lhs in
	  let rhs = term2token ctxt rhs Alone in
	  Box ([Verbatim "\\"] @ lhs @ [ Space 1; Verbatim "->"; Space 1; rhs])
	)

    | Match (te, eqs, _) ->
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation _ -> withParen
	| _ -> fun x -> x
      ) (
	Box [Verbatim "match"; Space 1; term2token ctxt te Alone; Space 1; Verbatim "with"; Newline;
	     Box (intercalate Newline (List.map (fun (p, te) ->
	       Box [Verbatim "|"; Space 1; pattern2token ctxt p Alone; Space 1; Verbatim ":="; Space 1; term2token ctxt te Alone ]
	     ) eqs
	     )
	     )	  
	    ]
       )
	(*
    | AVar _ -> raise (Failure "term2token - catastrophic: still an AVar in the term")
    | TName _ -> raise (Failure "term2token - catastrophic: still an TName in the term")
	*)
    | AVar _ -> Verbatim "_"
    | TName (s, _) -> Verbatim (symbol2string s)

and pattern2token (ctxt: context) (pattern: pattern) (p: place) : token =
  match pattern with
    | PType _ -> Verbatim "Type"
    | PVar (n, _, _) -> Verbatim n
    | PAVar _ -> Verbatim "_"
    | PCste (s, _) -> Verbatim (symbol2string s)
    | PAlias (n, pattern, _, _) -> Box [Verbatim n; Verbatim "@"; pattern2token ctxt pattern InAlias]

    (* for the append we have several implementation that mimics the ones for terms *)
    | PApp ((Symbol (s, Infix (myprio, myassoc)), _), args, _, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 2->
      (* we should put parenthesis in the following condition: *)
      (match p with
	(* if we are an argument *)
	| InArg Explicit -> withParen
	(* if we are in a notation such that *)
	(* a prefix or postfix binding more  than us *)
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	(* or another infix with higher priority *)
	| InNotation (Infix (i, _), _) when i > myprio -> withParen
	(* or another infix with same priority depending on the associativity and position *)
	(* I am the first argument and its left associative *)
	| InNotation (Infix (i, LeftAssoc), 1) when i = myprio -> withParen
	(* I am the second argument and its right associative *)
	| InNotation (Infix (i, RightAssoc), 2) when i = myprio -> withParen
	(* if we are in an alias *)
	| InAlias -> withParen

	(* else we do not need parenthesis *)
	| _ -> fun x -> x
      ) (
	match (if !pp_option.show_implicit then List.map fst args else filter_explicit args) with
	  | arg1::arg2::[] ->
	    let arg1 = pattern2token ctxt arg1 (InNotation (Infix (myprio, myassoc), 1)) in
	    let arg2 = pattern2token ctxt arg2 (InNotation (Infix (myprio, myassoc), 2)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg1; te; arg2])
	  | _ -> raise (DoudouException (FreeError "pattern2token, App infix case: irrefutable patten"))
       )
    (* the case for Prefix *)
    | PApp ((Symbol (s, (Prefix myprio)), _), args, _, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a postfix notation more binding than us
	 - in an alias
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InAlias -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	| _ -> fun x -> x
      ) (
	match (if !pp_option.show_implicit then List.map fst args else filter_explicit args) with
	  | arg::[] ->
	    let arg = pattern2token ctxt arg (InNotation (Prefix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [te; arg])
	  | _ -> raise (DoudouException (FreeError "pattern2token, App prefix case: irrefutable patten"))
       )

    (* the case for Postfix *)
    | PApp ((Symbol (s, (Postfix myprio)), _), args, _, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a prefix notation more binding than us
	 - in an alias
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| InAlias -> withParen
	| _ -> fun x -> x
      ) (
	match (if !pp_option.show_implicit then List.map fst args else filter_explicit args) with
	  | arg::[] ->
	    let arg = pattern2token ctxt arg (InNotation (Postfix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg; te])
	  | _ -> raise (DoudouException (FreeError "term2token, App postfix case: irrefutable patten"))
       )

    | PApp ((s, pos), args, _, _) when not !pp_option.show_implicit && List.length (filter_explicit args) = 0 ->
      term2token ctxt (Cste (s, pos)) p

    (* general case *)
    | PApp ((s, _), args, _, _) ->
      (* we only embed in parenthesis if
	 - we are an argument of an application
	 - we are in a notation (no !!! application more binding than operators)
      *)
      (match p with
	| InArg Explicit -> withParen
	| InAlias -> withParen
	| _ -> fun x -> x
      ) (
	let _, args = 
	  List.fold_left (
	    fun (ctxt, lst) te ->
	      input_pattern ctxt te, lst @ [pattern2token ctxt te (InArg Explicit)]
	  ) (ctxt, []) (if !pp_option.show_implicit then List.map fst args else filter_explicit args)
	in
	let s = symbol2string s in
	Box (intercalate (Space 1) (Verbatim s::args))
       )


(* make a string from a term *)
let term2string (ctxt: context) (te: term) : string =
  let token = term2token ctxt te Alone in
  let box = token2box token 80 2 in
  box2string box

let pattern2string (ctxt: context) (p: pattern) : string =
  let token = pattern2token ctxt p Alone in
  let box = token2box token 80 2 in
  box2string box

(* pretty printing for errors *)
let pos2token (p: pos) : token =
  match p with
    | ((-1, -1), (-1, -1)) -> Verbatim ""
    | (startp, endp) ->
      Box [Verbatim (string_of_int (fst startp)); 
	   Verbatim ":"; 
	   Verbatim (string_of_int (snd startp)); 
	   Verbatim "-"; 
	   Verbatim (string_of_int (fst endp)); 
	   Verbatim ":"; 
	   Verbatim (string_of_int (snd endp)); 
	  ]

    
let context2token (ctxt: context) : token =
  Box ([Verbatim "{"] 
       @ ( intercalates [Verbatim ";"; Newline]
	     (map_remain (fun hd tl ->
	       Box [Verbatim "(";
		    Verbatim (symbol2string hd.symbol); Space 1; Verbatim ":="; Space 1; term2token (hd::tl) hd.value Alone; Space 1; Verbatim "::"; Space 1; term2token (hd::tl) hd.ty Alone; Newline;
		    Box (intercalates [Verbatim ";"; Newline] (List.map (fun (i, ty, te) -> 
		      Box [Verbatim "(";
			   Verbatim (string_of_int i); Space 1; Verbatim "=>"; Space 1; term2token (hd::tl) te Alone; Space 1; Verbatim "::"; Space 1; term2token (hd::tl) ty Alone;
			   Verbatim ")"
			  ]
		    ) hd.fvs)
		    );
		    Verbatim ")"		    
		   ]
	      ) ctxt
	     )
       )	  
       @ [Verbatim "}"]
  )

let rec error2token (err: doudou_error) : token =
  match err with
    | NegativeIndexBVar i -> Verbatim "bvar as a negative index"
    | Unshiftable_term (te, level, delta) -> Verbatim "Cannot shift a term"
    | UnknownCste c -> Box [Verbatim "unknown constante:"; Space 1; Verbatim (symbol2string c)]

    | UnknownBVar (i, ctxt) -> Box [Verbatim "unknown bounded var:"; Space 1; Verbatim (string_of_int i); Space 1; context2token ctxt]
    | UnknownFVar (i, ctxt) -> Verbatim "UnknownFVar"

    | UnknownUnification (ctxt, te1, te2) ->
      Box [
	Verbatim "Do not know how to unify"; Newline;
	pos2token (get_term_pos te1); Space 1; term2token ctxt te1 Alone; Newline;
	pos2token (get_term_pos te2); Space 1; term2token ctxt te2 Alone; Newline
      ]
    | NoUnification (ctxt, te1, te2) ->
      Box [
	Verbatim "Cannot unify"; Newline;
	pos2token (get_term_pos te1); Space 1; term2token ctxt te1 Alone; Newline;
	pos2token (get_term_pos te2); Space 1; term2token ctxt te2 Alone; Newline
      ]
    | NoMatchingPattern (ctxt, p, te) ->
      Box [
	Verbatim "Cannot unify:"; Newline;	
	pos2token (get_pattern_pos p); Space 1; pattern2token ctxt p Alone; Newline;
	pos2token (get_term_pos te); Space 1; term2token ctxt te Alone;
      ]
    | CannotInfer (ctxt, te, err) ->
      Box [
	Verbatim "cannot infer type for:"; Space 1;
	pos2token (get_term_pos te); Space 1; term2token ctxt te Alone; Newline;
	Verbatim "reason:"; Newline;
	error2token err
      ]
    | CannotTypeCheck (ctxt, te, inferedty, ty, err) ->
      Box [
	Verbatim "the term:"; Space 1;
	pos2token (get_term_pos te); Space 1; term2token ctxt te Alone; Newline;
	Verbatim "of infered type:"; Space 1;
	term2token ctxt inferedty Alone; Newline;
	Verbatim "cannot be typecheck with type:"; Space 1;
	pos2token (get_term_pos ty); Space 1; term2token ctxt ty Alone; Newline;
	Verbatim "reason:"; Newline;
	error2token err
      ]
    | FreeError s -> Verbatim s
    | _ -> Verbatim "Internal error"

let equation2token (ctxt: context) (eq: equation) : token =
  let (p, te) = eq in
  Box [pattern2token ctxt p Alone; Space 1; Verbatim ":="; Space 1;
       let ctxt = input_pattern ctxt p in term2token ctxt te Alone]

let defs2token (defs: defs) : token =
  (* fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c *)
  Box (
    Hashtbl.fold (fun key value acc ->
      match value with
	| (s, ty, Equation [PCste (s', _), te]) ->
	  acc @ [Box [Verbatim (symbol2string s); Space 1; Verbatim ":="; term2token [] te Alone; Space 1; Verbatim "::"; Space 1; term2token [] ty Alone]; Newline]
	| (s, ty, _) ->
	  acc @ [Box [Verbatim (symbol2string s); Space 1; Verbatim "::"; Space 1; term2token [] ty Alone]; Newline]
    ) defs.store [] @ 
      [Newline] @
      (intercalate (Space 1) (List.map (fun s -> Verbatim (symbol2string s)) (List.flatten defs.hist)))
  )  

(* make a string from an error *)
let error2string (err: doudou_error) : string =
  let token = error2token err in
  let box = token2box token 80 2 in
  box2string box

let judgment2string (ctxt: context) (te: term) (ty: term) : string =
  let token = Box [Verbatim "|-"; Space 1; term2token ctxt te Alone; Space 1; Verbatim "::"; Space 1; term2token ctxt ty Alone] in
  let box = token2box token 80 2 in
  box2string box

let context2string (ctxt: context) : string =
  let token = context2token ctxt in
  let box = token2box token 80 2 in
  box2string box

let equation2string (ctxt: context) (eq: equation) : string =
  let token = equation2token ctxt eq in
  let box = token2box token 80 2 in
  box2string box

let defs2string (defs: defs) : string =
  let token = defs2token defs in
  let box = token2box token 80 2 in
  box2string box

let _ = term2string_ptr := term2string
