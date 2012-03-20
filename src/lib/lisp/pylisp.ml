open Pycaml;;
open Printf;;
open Libparser;;
open Lisp;;

let ctxt = init_ctxt () ;;

let pyobject_registry : (int, (expr * int)) Hashtbl.t = Hashtbl.create 100;;

let debug = ref false;;

let show_pyobject_registry () =
  (* iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit *)
  Hashtbl.iter (fun id (te, rc) ->
    let s = expr2string te in
    printf "%d: %s, %d\n" id s rc; flush Pervasives.stdout;    
  ) pyobject_registry;
    printf "\n\n"; flush Pervasives.stdout
;;

let register (te: expr) : int =  
  let id = Hashtbl.hash te in
  if !debug then printf "id for %s --> %d\n" (expr2string te) id;
  if Hashtbl.mem pyobject_registry id then (
    if eq te (fst (Hashtbl.find pyobject_registry id)) then
      id 
    else (
      let id = ref (Random.int 10000000) in
      while Hashtbl.mem pyobject_registry !id do
	id := Random.int 10000000
      done;
      let _ = Hashtbl.add pyobject_registry !id (te, 1) in
      !id  
    )
  ) else   
    let _ = Hashtbl.add pyobject_registry id (te, 1) in
    id  
;;

let marshal_expr_python createValue te =
  let id = register te in
  if !debug then printf "registered %s (%d)\n" (expr2string te) id;
  let res = pycallable_asfun createValue [| pyint_fromint id |] in
  if !debug then printf "created Value for id %d\n" id;
  res
;;

let marshal_python_expr valueClass value =
  let isValue = pyobject_isinstance (value, valueClass) in
  if isValue = 1 then
    let id_object = pyobject_getattr (value, pystring_fromstring "id") in
    let id = pyint_asint id_object in
    if not (Hashtbl.mem pyobject_registry id) then
      raise (Failure "marshal_python_doudou: unknown id")
    else
      let (te, _) = Hashtbl.find pyobject_registry id in
      te        
  else
    raise (Failure "marshal_python_doudou: only marshaling of Value instance for now ...")
;;

(***************************************************************)

let _ = python_exec "class Value:
     # just register the id
     # the id should be already registered in ocaml
     def __init__(self, id):
         #print \"python: register \" + str(id) + \": \" + Lisp.to_string(id) 
         #print \"python: registering \" + str(id)
         self.id=id

     # decref the term registered by id
     def __del__(self):
         #print \"__del__(\" + str(self.id) + \")\"
         try:
             Lisp.decref(self.id)
         except:
             return None

     # return the string representation
     def __str__(self):
         return Lisp.to_string(self.id)

     # application (here args is a tuple)
     def __call__(self, *args):
         return Lisp.apply(self.id, args)

     # size of the term (1 + number of explicite arguments)
     # def __len__(self):
     #    return Lisp.length(self.id)

def createValue(id):
    return Value(id)



  ";;

let mdl = pyimport_addmodule "Lisp";;
let lisp_dict = pymodule_getdict mdl;;
 
let value_class = python_eval "Value";;
let createValue_function = python_eval "createValue";;

(***************************************************)

let _ = 
  python_interfaced_function 
    ~register_as:"Lisp.apply"
    ~docstring:"application of a registered term with python arguments"
    [|IntType; TupleType|]
    (fun args ->
      match args with
	| [| id; args |] ->
	  let id = pyint_asint id in
	  if not (Hashtbl.mem pyobject_registry id) then (
	    raise (Failure "Lisp.apply: unknown id")
	  )
	  else (
	    let args = pytuple_toarray args in
	    let args = Array.map (fun arg -> marshal_python_expr value_class arg) args in
	    let te = List ((fst (Hashtbl.find pyobject_registry id))::(Array.to_list args)) in
	    try
	      let te = eval te ctxt in
	      let pte = marshal_expr_python createValue_function te in
	      pte
	    with
	      | LispException err -> 
		raise (Failure (error2string err))
	      | Failure s -> 
		raise (Failure s)
	      | _ -> 
		raise (Failure "Lisp.apply: unknown exception")
	  )
	    
	| _ -> raise (Failure "Lisp.apply: wrong arguments")
    )
;;

let _ = 
  python_interfaced_function 
    ~register_as:"Lisp.to_string"
    ~docstring:"returns string representation of a registered term"
    [|IntType|]
    (fun [| id |] ->
      let id = pyint_asint id in
      if not (Hashtbl.mem pyobject_registry id) then (
	raise (Failure "Lisp.to_string: unknown id")
      )
      else (
	pystring_fromstring (expr2string (fst (Hashtbl.find pyobject_registry id)))
      )
    )
;;


let _ = 
  python_interfaced_function 
    ~register_as:"Lisp.decref"
    ~docstring:"decrement the ref. counter of a registered term"
    [|IntType|]
    (fun [| id |] ->
      let id = pyint_asint id in
      if not (Hashtbl.mem pyobject_registry id) then (
	raise (Failure "Lisp.decref: unknown id")
      )
      else (
	let (value, refcounter) = Hashtbl.find pyobject_registry id in
	let _ = if refcounter = 1 then
	    Hashtbl.remove pyobject_registry id		    
	  else
	    Hashtbl.replace pyobject_registry id (value, refcounter - 1) in
	pynone ()
      )
    )
;;

let _ =
    python_interfaced_function 
      ~register_as:"Lisp.eval"
      ~docstring:"enter a term"
      [|StringType|]
      (fun [| str |] ->
	let str = pystring_asstring str in
	(* we set the parser *)
	let lines = stream_of_string str in
	let pb = build_parserbuffer lines in
	try
	  let es = many1 parse_expr pb in
	  let res = List.map (fun hd -> eval hd ctxt) es in
	  let res = List.nth res (List.length res - 1) in
	  marshal_expr_python createValue_function res	  
	with
	  (* TODO: return proper python exception *)
	  | NoMatch -> 
	    raise (Failure (String.concat "\n" ["parsing error in:"; Buffer.contents pb.bufferstr; markerror pb]))
	  | LispException err -> 
	    raise (Failure (error2string err))
      )
;;


let _ = python_exec "import Lisp";;

pymain Sys.argv;;
