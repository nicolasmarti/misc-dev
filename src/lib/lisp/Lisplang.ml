open Pycaml
open Libparser

module L = struct
    
  let ctxt = ref (Lisp.init_ctxt ())

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
  let init () = (ctxt := Lisp.init_ctxt ())

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
    Lisp.eval e !ctxt
    

  let definition s = 0

  let undo_definition () = ()

end
