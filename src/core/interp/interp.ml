open Pycaml;;

open Def;;
open Misc;;
open Pprinter;;
open Printf;;
open Engine;;
open Libparser;;
open Parser;;
open Entry;;
open Context;;

let defs = ref (empty_defs ());;

let ctxt = ref empty_context;;

let pyobject_registry : (int, (term * int)) Hashtbl.t = Hashtbl.create 100;;

let debug = ref false;;

let show_pyobject_registry () =
  (* iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit *)
  Hashtbl.iter (fun id (te, rc) ->
    let s = term2string !ctxt te in
    printf "%d: %s, %d\n" id s rc; flush Pervasives.stdout;    
  ) pyobject_registry;
    printf "\n\n"; flush Pervasives.stdout
;;

let register (te: term) : int =  
  let id = Hashtbl.hash te in
  if !debug then printf "id for %s --> %d\n" (term2string !ctxt te) id;
  if Hashtbl.mem pyobject_registry id then (
    if equality_term_term !defs ctxt te (fst (Hashtbl.find pyobject_registry id)) then
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

let marshal_doudou_python createValue te =
  let id = register te in
  if !debug then printf "registered %s (%d)\n" (term2string !ctxt te) id;
  let res = pycallable_asfun createValue [| pyint_fromint id |] in
  if !debug then printf "created Value for id %d\n" id;
  res
;;

let marshal_python_doudou valueClass value =
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
         #print \"python: register \" + str(id) + \": \" + Doudou.to_string(id) 
         #print \"python: registering \" + str(id)
         self.id=id

     # decref the term registered by id
     def __del__(self):
         #print \"__del__(\" + str(self.id) + \")\"
         Doudou.decref(self.id)

     # return the string representation
     def __str__(self):
         return Doudou.to_string(self.id)

     def type(self):
         return Doudou.type(self.id)

     # application (here args is a tuple)
     def __call__(self, *args):
         return Doudou.apply(self.id, args)

     # size of the term (1 + number of explicite arguments)
     # def __len__(self):
     #    return Doudou.length(self.id)

def createValue(id):
    return Value(id)



  ";;

let mdl = pyimport_addmodule "Doudou";;
let doudou_dict = pymodule_getdict mdl;;
 
let value_class = python_eval "Value";;
let createValue_function = python_eval "createValue";;

let _ = pydict_setitemstring (doudou_dict, "Type", marshal_doudou_python value_class (Type nopos));;

(***************************************************)

let _ = 
  python_interfaced_function 
    ~register_as:"Doudou.apply"
    ~docstring:"application of a registered term with python arguments"
    [|IntType; TupleType|]
    (fun args ->
      match args with
	| [| id; args |] ->
	  let id = pyint_asint id in
	  if not (Hashtbl.mem pyobject_registry id) then (
	    raise (Failure "Doudou.apply: unknown id")
	  )
	  else (
	    let args = pytuple_toarray args in
	    let args = Array.map (fun arg -> marshal_python_doudou value_class arg) args in
	    let te = App (
	      fst (Hashtbl.find pyobject_registry id),
	      List.map (fun hd -> (hd, Explicit)) (Array.to_list args),
	      nopos) in
	    let saved_ctxt = !ctxt in
	    let saved_defs = copy_defs !defs in
	    try
	      (* we infer the term type *)
	      let te, ty = typeinfer !defs ctxt te in
	      let te = reduction !defs ctxt clean_term_strat te in
	      let pte = marshal_doudou_python createValue_function te in
	      pte
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
		raise (Failure "Doudou.apply: unknown exception")
	  )
	    
	| _ -> raise (Failure "Doudou.apply: wrong arguments")
    )
;;

let _ = 
  python_interfaced_function 
    ~register_as:"Doudou.to_string"
    ~docstring:"returns string representation of a registered term"
    [|IntType|]
    (fun [| id |] ->
      let id = pyint_asint id in
      if not (Hashtbl.mem pyobject_registry id) then (
	raise (Failure "Doudou.apply: unknown id")
      )
      else (
	pystring_fromstring (term2string !ctxt (fst (Hashtbl.find pyobject_registry id)))
      )
    )
;;

let _ = 
  python_interfaced_function 
    ~register_as:"Doudou.type"
    ~docstring:"returns the type of a registered term"
    [|IntType|]
    (fun [| id |] ->
      let id = pyint_asint id in
      if not (Hashtbl.mem pyobject_registry id) then (
	raise (Failure "Doudou.type: unknown id")
      )
      else (
	let te = fst (Hashtbl.find pyobject_registry id) in
	let _, ty = typeinfer !defs ctxt te in
	marshal_doudou_python value_class ty
      )
    )
;;

let _ = 
  python_interfaced_function 
    ~register_as:"Doudou.decref"
    ~docstring:"decrement the ref. counter of a registered term"
    [|IntType|]
    (fun [| id |] ->
      let id = pyint_asint id in
      if not (Hashtbl.mem pyobject_registry id) then (
	raise (Failure "Doudou.decref: unknown id")
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
      ~register_as:"Doudou.proceed"
      ~docstring:"enter a definition"
      [|StringType|]
      (fun [| str |] ->
	let str = pystring_asstring str in
	(* we set the parser *)
	let lines = stream_of_string str in
	(* we save the context and the defs *)
	let saved_ctxt = !ctxt in
	let saved_defs = copy_defs !defs in
	(*if verbose then printf "input:\n%s\n" str;*)
	let pb = build_parserbuffer lines in
	try
	  let (consumed, def) = parse_onedefinition !defs pb in
	  let symbs = process_definition ~verbose:false defs ctxt def in
	  let consumed = pyint_fromint consumed in
	  let _ = List.map (fun symb ->
	    let s = (symbol2string symb) in
	    (*printf "registering %s\n" s;*)
	    let te = Cste (symb, nopos) in
	    try 
	      let pte = marshal_doudou_python createValue_function te in
	      let _ = pydict_setitemstring (doudou_dict, s, pte) in
	      ()
	    with
	      | _ -> (*printf "failed registerig %s\n" s; flush Pervasives.stdout;*) ()
	  ) symbs in
	  consumed
	    with
	      (* TODO: return proper python exception *)
	      | NoMatch -> 
		raise (Failure (String.concat "\n" ["parsing error in:"; Buffer.contents pb.bufferstr; errors2string pb]))
	      | DoudouException err -> 
	      (* we restore the context and defs *)
		ctxt := saved_ctxt;
		defs := saved_defs;
		raise (Failure (error2string err))
      )
;;

let _ = 
  python_interfaced_function 
    ~register_as:"Doudou.undo"
    ~docstring:"undo last defs"
    [||]
    (fun [| |] ->
      try 
	let symbs = undoDefinition defs in
	let _ = List.map (fun symb ->
	  let s = symbol2string symb in
	  try 
	    let _ = pydict_delitemstring (doudou_dict, s) in
	    ()
	  with
	    | _ -> (*printf "failed unregisterig %s\n" s; flush Pervasives.stdout;*) ()
	) symbs in
	pynone ()
      with
	| DoudouException err -> 
	  (* we restore the context and defs *)
	  raise (Failure (error2string err))

    )
;;  

let _ = python_exec "import Doudou";;

open Primitive_float;;
