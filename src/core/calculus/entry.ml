open Def
open Misc
open Context
open Engine
open Parser
open Libparser
open Pprinter
open Extlist
open Printf

(******************************************)
(*         entry functions                *)
(******************************************)

open Stream

(* the strategy to cleanup types *)
let clean_term_strat : reduction_strategy = {
  beta = Eager;
  betastrong = true;
  delta = true;
  iota = true;
  deltaiotaweak = false;
  deltaiotaweak_armed = false;
  zeta = true;
  eta = true;
}

let rec process_definition ?(verbose: bool = false) (defs: defs ref) (ctxt: context ref) (definition: definition) : symbol list =
  match definition with
    | DefInductive (s, args, ty, constrs) -> (
      (* first, we build the inductive type's type and typecheck again type *)
      let ind_ty = build_impls args ty in
      let ind_ty, _ = typecheck !defs ctxt ind_ty (Type nopos) in
      (* first we push the type, so that results of all further unification will be aplpied on it *)
      push_terms ctxt [ind_ty];
      (* then we grab back the quantifiers and body of the type *)
      let args, ty = destruct_impl ~nb_qs:(List.fold_left (fun acc (args, _, _) -> acc + List.length args) 0 args) ind_ty in
      (* we pushes the quantifications *)
      let _ = List.map (fun q -> push_quantification q ctxt) args in      
      (* we create a new defs, where the inductive types is an axiom of the proper type *)
      addAxiom defs s ind_ty;
      (* we traverse the constructors, typing them and looking for there well-formness 
	 N.B.: there is no positivity test yet
      *)
      let constrs = List.map (fun (s', ty) -> 
	(* any constructors should have type type *)
	let ty, _ = typecheck !defs ctxt ty (Type nopos) in
	(* check for well formness, first we destruct the impl *)
	let hyps, ccl = destruct_impl ty in
	(* then we look at the ccl, we destruct it *)
	let hd, args' = destruct_app ccl in
	(* first we need to be sure that the head of the application is the inductive *)
	let _ = match hd with
	  | Cste (s'',_) when s = s'' -> ()
	  | Cste (s'', _) -> raise (DoudouException (FreeError (
	    String.concat "" ["error in inductive type ";
			      symbol2string s; 
			      " definition of constructor ";
			      symbol2string s'; 
			      " of type ";
			      (term2string !ctxt ty);
			      "\nthe constructor conclusion head is not the inductive type but ";
			      symbol2string s''
			     ]
	  )))
	  | _ -> raise (DoudouException (FreeError (
	    String.concat "" ["error in inductive type ";
			      symbol2string s; 
			      " definition of constructor ";
			      symbol2string s'; 
			      " of type ";
			      (term2string !ctxt ty);
			      "\nthe constructor conclusion head is not the inductive type (and not even a symbol)"
			     ]
	  )))
	in
	(* then we check that the first arguments are the same as the args of the inductive *)
	let _ = List.fold_left (fun acc ((constr_arg, n1), (_, _, n2, _)) ->
	  (* we check that both nature are the same *)
	  if n1 <> n2 then
	    raise (DoudouException (FreeError (
	      String.concat "" ["error in inductive type ";
				symbol2string s; 
				" definition of constructor ";
				symbol2string s'; 
				"\nthe ";
				string_of_int acc;
				"nth argument nature of the conclusion is not the same as the nature of the inductive argument"
			       ]
	    )))
	  else
	    (* and then that it is a variable correesponding to the inductive argument *)
	    match constr_arg with
	      | TVar (i, _) when i = List.length hyps + List.length args -1 - acc -> acc + 1
	      | _ -> raise (DoudouException (FreeError (
		String.concat "" ["error in inductive type ";
				  symbol2string s; 
				  " definition of constructor ";
				  symbol2string s'; 
				  "\nthe ";
				  string_of_int acc;
				  "nth argument of the conclusion is not the same as the argument of the inductive argument: ";
				  (term2string !ctxt (TVar ( List.length hyps + List.length args -1 - acc, nopos)))
				 ]
	      )))
	  
	) 0 (List.combine (take (List.length args) args') args) in

	(*printf "constructor %s of inductive type %s has type: %s\n" (symbol2string s') (symbol2string s) (term2string !ctxt ty);*)
	s', ty
      ) constrs in
      (* we remove the definition of the inductive type *)
      let _ = undoDefinition defs in
      (* now we can pop the quantifiers *)
      let qs = List.rev (List.map (fun _ -> fst (pop_quantification ctxt [])) args) in
      (* pop the inductive types type *)
      let [ind_ty] = pop_terms ctxt 1 in
      if verbose then printf "Inductive: %s :: %s\n" (symbol2string s) (term2string !ctxt ind_ty);      
      (* requantify the args as Implicit in the contructors *)
      let constrs = List.map (fun (s, ty) ->
	let ty = build_impls (List.map (fun (s, ty, _, _) -> [s, nopos], ty, Implicit) qs) ty in
	if verbose then printf "Constructor: %s :: %s\n" (symbol2string s) (term2string !ctxt ty);      

	s, ty
      ) constrs in
      (* and we update the definitions *)
      addInductive defs s ind_ty constrs;
      List.hd !defs.hist
    )

    | DefSignature (s, ty) ->
      (* we typecheck the type against Type *)
      let ty, _ = typecheck !defs ctxt ty (Type nopos) in	  
      (* we flush the free vars so far *)
      let [ty] = flush_fvars ctxt [ty] in
      (* add to the defs *)
      addAxiom defs s ty;
      (* just print that everything is fine *)
      if verbose then printf "Axiom: %s :: %s \n" (symbol2string s) (term2string !ctxt ty); flush Pervasives.stdout;
      List.hd !defs.hist

    | DefEquation (PCste (s, spos) as p, te) | DefEquation (PApp ((s, spos), _, _, _) as p, te) ->
      let p, te = typecheck_equation !defs ctxt p te in
      (* we flush the free vars so far *)
      let [] = flush_fvars ctxt [] in
      (* add to the defs *)
      addEquation defs s (p, te);
      (* just print that everything is fine *)
      if verbose then printf "Equation: %s \n" (equation2string !ctxt (p, te)); flush Pervasives.stdout;
      []
      
    | DefTerm te ->
      (* we infer the term type *)
      let te, ty = typeinfer !defs ctxt te in
      let te = reduction !defs ctxt clean_term_strat te in
      let ty = reduction !defs ctxt clean_term_strat ty in
      (* we flush the free vars so far *)
      let [te; ty] = flush_fvars ctxt [te; ty] in
      (* just print that everything is fine *)
      if verbose then printf "Term |- %s :: %s \n" (term2string !ctxt te) (term2string !ctxt ty); flush Pervasives.stdout;
      []

    | Load filename ->
      load_definitions defs ctxt ~verbose:verbose (String.concat "." [filename; "doudou"]);
      List.hd !defs.hist

(* parse definition from a parserbuffer *)
and parse_process_definition (defs: defs ref) (ctxt: context ref) ?(verbose: bool = false) (pb: parserbuffer) : unit =
  (* consume all the whatspace and grab the position *)
  let () = whitespaces pb in
  let pos = cur_pos pb in
  (*if verbose then printf "input:\n%s\n" str;*)
  (* we save the context and the defs *)
  let saved_ctxt = !ctxt in
  let saved_defs = copy_defs !defs in
  try
    let def = parse_definition !defs pos pb in
    let _ = process_definition ~verbose:verbose defs ctxt def in
    assert (List.length !ctxt = 1)
  with
    | NoMatch -> 
      if verbose then printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb); flush Pervasives.stdout;
      raise NoMatch
    | DoudouException err -> 
      (* we restore the context and defs *)
      ctxt := saved_ctxt;
      defs := saved_defs;
      if verbose then printf "error:\n%s\n" (error2string err);
      raise (DoudouException err)

(* the same function but with a string *)
and parse_process_definition_from_string (defs: defs ref) (ctxt: context ref) ?(verbose: bool = false) (str: string) : unit =
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  parse_process_definition defs ctxt ~verbose:verbose pb

(* the same function but with a filename *)
and parse_process_definition_from_file (defs: defs ref) (ctxt: context ref) ?(verbose: bool = false) (filename: string) : unit =    
  let ic = try Pervasives.open_in filename with | Sys_error s -> raise (DoudouException (FreeError s)) in
  let lines = line_stream_of_channel ic in
  let pb = build_parserbuffer lines in
  parse_process_definition defs ctxt ~verbose:verbose pb

(* parse all the definitions until an eof *)
and parse_process_definitions (defs: defs ref) (ctxt: context ref) ?(verbose: bool = false) (pb: parserbuffer) : unit =
    (* we save the context and the defs *)
    let saved_ctxt = !ctxt in
    let saved_defs = copy_defs !defs in
    let continue = ref true in
    while !continue do
      try
	(* process one definition *)
	parse_process_definition defs ctxt ~verbose:verbose pb;
	assert (List.length !ctxt = 1)
      with
	| NoMatch -> (
	  try 
	    let () = whitespaces pb in
	    let () = eos pb in
	    continue := false
	  with
	    | NoMatch ->
	      if verbose then printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb); flush Pervasives.stdout;
	      raise (DoudouException (FreeError (errors2string pb)))
	)
	| DoudouException err ->
	  (* we restore the context and defs *)
	  ctxt := saved_ctxt;
	  defs := saved_defs;
	  if verbose then printf "error:\n%s\n" (error2string err); flush Pervasives.stdout;
	  raise (DoudouException err)	  
    done

(* the same function but with a string *)
and parse_process_definitions_from_string (defs: defs ref) (ctxt: context ref) ?(verbose: bool = false) (str: string) : unit =
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  parse_process_definitions defs ctxt ~verbose:verbose pb

(* the same function but with a filename *)
and parse_process_definitions_from_file (defs: defs ref) (ctxt: context ref) ?(verbose: bool = false) (filename: string) : unit =
  let ic = try Pervasives.open_in filename with | Sys_error s -> raise (DoudouException (FreeError s)) in
  let lines = line_stream_of_channel ic in
  let pb = build_parserbuffer lines in
  parse_process_definitions defs ctxt ~verbose:verbose pb

(* this function load a source file, and flatten the new definitions into one historic event *)
and load_definitions (defs: defs ref) (ctxt: context ref) ?(verbose: bool = false) (filename: string) : unit =
  (* first we compute the current historic size *)
  let hist_size = List.length !defs.hist in
  (* then we parse and process definitions *)
  parse_process_definitions_from_file defs ctxt ~verbose:verbose filename;
  (* then we flatten the historic from the file into one element *)
  let hd = take (List.length !defs.hist - hist_size) !defs.hist in
  let tl = drop (List.length !defs.hist - hist_size) !defs.hist in
  defs := {!defs with hist = (List.flatten hd)::tl}
