open Pycaml
open Def;;
open Misc;;
open Pprinter;;
open Printf;;
open Engine;;
open Libparser;;
open Parser;;
open Entry;;
open Context;;

module L = struct


  let ctxt = ref empty_context;;
    
  let defs = ref (empty_defs ());;
  
  open Primitive_float;;
  
  Hashtbl.add (!defs).store "Float" (Name "Float", floattypeobj#get_type, Primitive floattypeobj#my_self);;

  (* the name of the language *)
  let name = "Calculus"

  (* the error and exception, plus a format function *)
  type error = doudou_error
  exception Exception = DoudouException

  let error2string = error2string

  type ty = term
  type value = term

  let ty2string ty = term2string !ctxt ty
  let value2string v = term2string !ctxt v

    
  let init () =
    ctxt := empty_context;
    defs := (empty_defs ());
    Hashtbl.add (!defs).store "Float" (Name "Float", floattypeobj#get_type, Primitive floattypeobj#my_self)


  let eq_value v1 v2 = equality_term_term !defs ctxt v1 v2

  let marshal_to_python v = None
  let marshal_from_python o = None

  let apply f args = 
    let te = App (f, 
		  List.map (fun hd -> (hd, Explicit)) (Array.to_list args),
		  nopos) in
    let saved_ctxt = !ctxt in
    let saved_defs = copy_defs !defs in
    try
      (* we infer the term type *)
      let te, ty = typeinfer !defs ctxt te in
      reduction !defs ctxt clean_term_strat te
    with
      | DoudouException err -> 
	(* we restore the context and defs *)
	ctxt := saved_ctxt;
	defs := saved_defs;
	raise (Failure (error2string err))
      | Failure s -> 
	ctxt := saved_ctxt;
	defs := saved_defs;
	raise (Failure s)
      | _ -> 
	ctxt := saved_ctxt;
	defs := saved_defs;
	raise (Failure "calculus.apply: unknown exception")

  let eval s = 
    (* we set the parser *)
    let lines = stream_of_string s in
    (* we save the context and the defs *)
    let saved_ctxt = !ctxt in
    let saved_defs = copy_defs !defs in
    (*if verbose then printf "input:\n%s\n" str;*)
    let pb = build_parserbuffer lines in
    try
      let startpos = cur_pos pb in

      let te = parse_term !defs startpos pb in

      let te, ty = process_term defs ctxt te in

      te

    with
	  (* TODO: return proper python exception *)
      | NoMatch -> 
	raise (Failure (String.concat "\n" ["parsing error in:"; Buffer.contents pb.bufferstr; markerror pb]))
      | DoudouException err -> 
	    (* we restore the context and defs *)
	ctxt := saved_ctxt;
	defs := saved_defs;
	raise (Failure (error2string err))



  let definition s =
    let lines = stream_of_string s in
    (* we save the context and the defs *)
    let saved_ctxt = !ctxt in
    let saved_defs = copy_defs !defs in
    (*if verbose then printf "input:\n%s\n" str;*)
    let pb = build_parserbuffer lines in
    try
      let (consumed, def) = parse_onedefinition !defs pb in
      let symbs = process_definition ~verbose:false defs ctxt def in
      let defined = List.map (fun symb ->
	let s = (symbol2string symb) in
	(*printf "registering %s\n" s;*)
	let te = Cste (symb, nopos) in
	s, te
      ) symbs in
      consumed, Array.of_list defined
    with
      (* TODO: return proper python exception *)
      | NoMatch -> 
	raise (Failure (String.concat "\n" ["parsing error in:"; Buffer.contents pb.bufferstr; markerror pb]))
      | DoudouException err -> 
	(* we restore the context and defs *)
	ctxt := saved_ctxt;
	defs := saved_defs;
	raise (Failure (error2string err))

  let undo_definition () = 
    ignore(undoDefinition defs)

end

