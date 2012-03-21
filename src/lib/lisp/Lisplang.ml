open Pycaml
open Libparser

module L = struct
    
  let ctxt = ref (Lisp.init_ctxt ())

  let saved_ctxt : (Lisp.env list) ref = ref []

  (* the name of the language *)
  let name = "Lisp"

  (* the error and exception, plus a format function *)
  type error = Lisp.lisp_error
  exception Exception = Lisp.LispException
      
  let error2string = Lisp.error2string

  (* the values and types *)
  type ty = unit
  type value = Lisp.expr

  (* functions to create a string from types and values *)
  let ty2string ty = ""
  let value2string = Lisp.expr2string

  (* initialization *)
  let init () = ctxt := Lisp.init_ctxt (); saved_ctxt := []

  (* equality over two values *)
  let eq_value v1 v2 = Lisp.eq v1 v2

  (* marshalling from/to python*)
  let marshal_to_python v = None
  let marshal_from_python o = None

  (* application *)
  let apply f args = Lisp.eval (Lisp.List (f::(Array.to_list args))) !ctxt

  (* eval *)
  let eval s =
    let lines = stream_of_string s in
    let pb = build_parserbuffer lines in
    let e = (
      try
	Lisp.parse_expr pb 
      with
	| NoMatch -> raise (Lisp.LispException (Lisp.StringError (markerror pb)))
    ) in
    let s_ctxt = !ctxt in
    try (
      let res = Lisp.eval e !ctxt in
      ctxt := s_ctxt;
      res    
    ) with | e -> ctxt := s_ctxt; raise e

  let definition s = 
    let s_ctxt = !ctxt in
    let lines = stream_of_string s in
    let pb = build_parserbuffer lines in
    let es = (
      try
	many1 Lisp.parse_expr pb 
      with
	| NoMatch -> 	  
	  raise (Lisp.LispException (Lisp.StringError (markerror pb)))
    ) in  
    try (
      let _ = List.map (fun hd -> Lisp.eval hd !ctxt) es in
      saved_ctxt := s_ctxt::!saved_ctxt;
      pb.beginpointer
    ) with | e -> ctxt := s_ctxt; raise e

  let undo_definition () = 
    ctxt := List.hd !saved_ctxt;
    saved_ctxt := List.tl !saved_ctxt

end
