open Opycaml.Api
open Def
open Misc
open Pprinter
open Printf
open Engine
open Libparser
open Parser
open Entry
open Context

let defs = ref (empty_defs ())

let ctxt = ref empty_context

let registry : (int, (term * int)) Hashtbl.t = Hashtbl.create 100

let debug = ref false

let show_registry () =
  (* iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit *)
  Hashtbl.iter (fun id (te, rc) ->
    let s = term2string !ctxt te in
    printf "%d: %s, %d\n" id s rc; flush Pervasives.stdout;    
  ) registry;
    printf "\n\n"; flush Pervasives.stdout

let register (te: term) : int =  
  let id = Hashtbl.hash te in
  if !debug then printf "id for %s --> %d\n" (term2string !ctxt te) id;
  if Hashtbl.mem registry id then (
    if equality_term_term !defs ctxt te (fst (Hashtbl.find registry id)) then
      id 
    else (
      let id = ref (Random.int 10000000) in
      while Hashtbl.mem registry !id do
	id := Random.int 10000000
      done;
      let _ = Hashtbl.add registry !id (te, 1) in
      !id  
    )
  ) else   
    let _ = Hashtbl.add registry id (te, 1) in
    id  

let marshal_doudou_python createValue te =
  let id = register te in
  if !debug then printf "registered %s (%d)\n" (term2string !ctxt te) id;
  let res = Object.call createValue [Object.obj (Int.fromLong id)] in
  if !debug then printf "created Value for id %d\n" id;
  res

let marshal_python_doudou valueClass value =
  try
    let isValue = Object.isInstance value valueClass in
    if isValue then
      let id_object = Object.getAttr value (Py.String.fromString "id") in
      let id = Int.asLong (Int.coerce id_object) in
      if not (Hashtbl.mem registry id) then
	None
      else
	let (te, _) = Hashtbl.find registry id in
	Some te        
    else
      None
  with
    | _ -> None

(***************************************************************)

let init_interp () =

  (*
    we need a python class that represents Doudou values
    c.f. http://docs.python.org/reference/datamodel.html#basic-customization

  *)

  let _ = Run.simpleString "class Value:
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
     def __len__(self):
         return Doudou.length(self.id)

def createValue(id):
    return Value(id)



  " in

  (* building Doudou module *)
  let mdl = Module.new_ "Doudou" in
  let mdldic = Import.getModuleDict () in
  Dict.setItemString mdldic "Doudou" mdl;

  let doudou_dict = Module.getDict mdl in

  (* grabing Value *)
  let main_mdl = Import.importModule "__main__" in
  let main_dict = Module.getDict main_mdl in
  let value_class = unsafe_coerce (Dict.getItemString main_dict "Value") in

  let createValue_function = Callable.coerce (Dict.getItemString main_dict "createValue") in

  (* filling the module *)
  (*
    Module.setClosureString : [>_Module] t -> string -> ([>_Tuple] t -> _Object t) -> unit
    Module.setItemString : [>_Module] t -> string -> [>_Object] t -> unit
  *)

  Module.setItemString mdl "Type"
    (marshal_doudou_python value_class (Type nopos));

  (*show_registry ();*)

  (*  *)
  Module.setClosureString mdl "apply"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | id::args::[] when Number.check id && Tuple.check args -> (
	    let id = Int.asLong (Int.coerce id) in	    
	    if not (Hashtbl.mem registry id) then (
	      if !debug then printf "apply(1)\n";
	      Object.obj (Base.none ())
	    )
	    else (
	      let args = Tuple.to_list (Tuple.coerce args) in
	      let rev_args = List.fold_left (fun acc hd -> 
		match acc with
		  | None -> if !debug then printf "apply(2)\n"; None
		  | Some acc -> 
		    match marshal_python_doudou value_class hd with
		      | None -> if !debug then printf "apply(3)\n"; None
		      | Some te ->
			Some (te::acc)
	      ) (Some []) args in	      
	      match rev_args with
		| None -> (
		  Object.obj (Base.none ())
		)
		| Some l ->
		  let args = List.rev l in
		  let te = App (
		    fst (Hashtbl.find registry id),
		    List.map (fun hd -> (hd, Explicit)) args,
		    nopos
		  ) in
		  let saved_ctxt = !ctxt in
		  let saved_defs = copy_defs !defs in
		  (*if verbose then printf "input:\n%s\n" str;*)
		  try
		    (* we infer the term type *)
		    let te, ty = typeinfer !defs ctxt te in
		    if !debug then printf "typechecked application\n";
		    let te = reduction !defs ctxt clean_term_strat te in
		    if !debug then printf "reduced results\n";
		    let pte = marshal_doudou_python createValue_function te in
		    if !debug then printf "marshalled results\n";
		    pte
		  with
		    (* TODO: return proper python exception *)
		    | DoudouException err -> 
		      (* we restore the context and defs *)
		      ctxt := saved_ctxt;
		      defs := saved_defs;
		      if !debug then printf "apply(4)\n"; 
		      Object.obj (Base.none ())
		    | Failure s -> 
		      ctxt := saved_ctxt;
		      defs := saved_defs;
		      if !debug then printf "apply(6): %s\n" s; 
		      Object.obj (Base.none ())
		    | _ -> 
		      ctxt := saved_ctxt;
		      defs := saved_defs;
		      if !debug then printf "apply(5)\n"; 
		      Object.obj (Base.none ())

	    )
	  )
	  | _ -> 
	    Object.obj (Base.none ())
      )
      with
	| _ -> 
	  Object.obj (Base.none ())

    );

  Module.setClosureString mdl "to_string"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | id::[] when Number.check id -> (
	    let id = Int.asLong (Int.coerce id) in	    
	    if not (Hashtbl.mem registry id) then (
	      Object.obj (Base.none ())
	    )
	    else (
	      Object.obj (Py.String.fromString (term2string !ctxt (fst (Hashtbl.find registry id))))
	    )
	    )
	  | _ -> 
	    Object.obj (Base.none ())
      )
      with
	| _ -> 
	  Object.obj (Base.none ())

    );

  Module.setClosureString mdl "type"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | id::[] when Number.check id -> (
	    let id = Int.asLong (Int.coerce id) in	    
	    if not (Hashtbl.mem registry id) then (
	      Object.obj (Base.none ())
	    )
	    else (	      
	      let te = fst (Hashtbl.find registry id) in
	      let _, ty = typeinfer !defs ctxt te in
	      marshal_doudou_python value_class ty
	    )
	  )
	  | _ -> 
	    Object.obj (Base.none ())
      )
      with
	| _ -> 
	  Object.obj (Base.none ())	    
    );

  Module.setClosureString mdl "length"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | id::[] when Number.check id -> (
	    let id = Int.asLong (Int.coerce id) in	    
	    if not (Hashtbl.mem registry id) then (
	      Object.obj (Base.none ())
	    )
	    else (
	      let te = fst (Hashtbl.find registry id) in
	      let len = match te with
		| App (_, l, _) ->
		  1 + List.length (filter_explicit l)
		| _ -> 1 
	      in
	      Object.obj (Int.fromLong len)
	    )
	    )
	  | _ -> 
	    Object.obj (Base.none ())
      )
      with
	| _ -> 
	  Object.obj (Base.none ())

    );

  Module.setClosureString mdl "decref"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | id::[] when Number.check id -> (
	    let id = Int.asLong (Int.coerce id) in
	    if !debug then printf "decref of %d\n" id;
	    if not (Hashtbl.mem registry id) then
	      Object.obj (Base.none ())
	    else
	      let (value, refcounter) = Hashtbl.find registry id in
	      let _ = if refcounter = 1 then
		  Hashtbl.remove registry id		    
		else
		  Hashtbl.replace registry id (value, refcounter - 1) in
	      Object.obj (Base.none ())
	    )
	  | _ -> Object.obj (Base.none ())
      )
      with
	| _ -> Object.obj (Base.none ())

    );

  (* enter a doudou definition *)
  Module.setClosureString mdl "proceed"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | str::_ when Py.String.check str -> (
	    let str = Py.String.asString (Py.String.coerce str) in
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
	      let o = Object.obj (Base.none ()) in
	      let consumed = Int.fromLong consumed in

	      let _ = List.map (fun symb ->
		let s = (symbol2string symb) in
		(*printf "registering %s\n" s;*)
		let te = Cste (symb, nopos) in
		try 
		  let pte = marshal_doudou_python createValue_function te in
		  Module.setItemString mdl s pte;
		  (*printf "registered %s\n" s*)
		with
		  | _ -> (*printf "failed registerig %s\n" s; flush Pervasives.stdout;*) ()
	      ) symbs in
	
	      Object.obj (Tuple.from_list [Object.obj consumed; o])	    
	    with
	      (* TODO: return proper python exception *)
	      | NoMatch -> 
		printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb);
		Object.obj (Py.String.fromString (errors2string pb))
	      | DoudouException err -> 
	      (* we restore the context and defs *)
		ctxt := saved_ctxt;
		defs := saved_defs;
		printf "error:\n%s\n" (error2string err); flush Pervasives.stdout;
		Object.obj (Py.String.fromString (error2string err))
	  )
	  | _ -> Object.obj (Base.none ())
      )
      with
	| _ -> Object.obj (Base.none ())

    );

  (* undo last definition *)
  Module.setClosureString mdl "undo"
    (fun args ->
      try 
	let symbs = undoDefinition defs in
	let _ = List.map (fun symb ->
	  let s = symbol2string symb in
	  try 
	    Dict.delItemString doudou_dict s
	  with
	    | _ -> (*printf "failed unregisterig %s\n" s; flush Pervasives.stdout;*) ()
	) symbs in
	Object.obj (Base.none ())
      with
	| DoudouException err -> 
	  (* we restore the context and defs *)
	  printf "error:\n%s\n" (error2string err); flush Pervasives.stdout;
	  Object.obj (Py.String.fromString (error2string err))
    );

  (* show definitions *)
  Module.setClosureString mdl "showdefs"
    (fun args ->
      let s = defs2string !defs in
      Object.obj (Py.String.fromString s)
    );


  (* importing Lisp module *)
  let _ = Run.simpleString "import Doudou" in
  ()
