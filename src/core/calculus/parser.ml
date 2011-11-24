open Def
open Extlist
open Misc
open Libparser

(**********************************)
(* parser (lib/parser.ml version) *)
(**********************************)

let at_start_pos (startp: (int * int)) (p: 'a parsingrule) : 'a parsingrule =
  fun pb ->
    let curp = cur_pos pb in
    if (snd startp > snd curp) then (
      (*printf "%d > %d\n" (snd startp) (snd curp);*)
      raise NoMatch
    );
    p pb

let after_start_pos (startp: (int * int)) (p: 'a parsingrule) : 'a parsingrule =
  fun pb ->
    let curp = cur_pos pb in
    if (snd startp >= snd curp) then (
      (*printf "%d >= %d\n" (snd startp) (snd curp);*)
      raise NoMatch
    );
    p pb

let with_pos (p: 'a parsingrule) : ('a * pos) parsingrule =
  fun pb ->
    let startp = cur_pos pb in
    let res = p pb in
    let endp = cur_pos pb in
    (res, (startp, endp))

let doudou_keywords = ["Type"; "::"; ":="; "->"; "match"; "with"]

open Str;;

let parse_reserved : unit parsingrule =
  foldp (List.map (fun x -> keyword x ()) doudou_keywords)

let name_parser : name parsingrule = applylexingrule (regexp "[a-zA-Z][a-zA-Z0-9]*", 
						      fun (s:string) -> 
							if List.mem s doudou_keywords then raise NoMatch else s
)

let parse_avar : unit parsingrule = applylexingrule (regexp "_", 
						     fun (s:string) -> ()
)

let parse_symbol_name (defs: defs) : symbol parsingrule =
  foldp (skipmap (fun s ->
    match s with
      | Name _ -> None
      | _ -> Some (tryrule (fun pb -> let () = word (symbol2string s) pb in s))
  ) (List.flatten defs.hist))

let parseint = applylexingrule (regexp "[0-9]+", fun (s:string) -> int_of_string s)
;;

let parseassoc : associativity parsingrule =
  foldp [
    tryrule (fun pb -> let () = whitespaces pb in 
		       let () = word "right" pb in 
		       let () = whitespaces pb in
		       RightAssoc
    );
    tryrule (fun pb -> let () = whitespaces pb in 
		       let () = word "left" pb in 
		       let () = whitespaces pb in
		       LeftAssoc
    );
    tryrule (fun pb -> let () = whitespaces pb in 
		       let () = word "no" pb in 
		       let () = whitespaces pb in
		       NoAssoc
    )
  ]


let parse_symbol_name_def : symbol parsingrule = 
  let symbols = ["\\+"; "\\*"; "\\["; "\\]";
		 "@"; "-"; ":"; "|"; "\\&"; "="; "~"; "\\\\"; "/"; "<"; ">"
		] in
  let format_symbols = String.concat "" ["\\("; 
					 String.concat "\\|" symbols;
					 "\\)*"
					] in
  let nofix = applylexingrule (regexp (String.concat "" ["\\["; format_symbols; "\\]"]), 
			       fun (s:string) -> String.sub s 1 (String.length s - 2)) in 
  let prefix = applylexingrule (regexp (String.concat "" ["\\["; format_symbols; ")"]), 
			       fun (s:string) -> String.sub s 1 (String.length s - 2)) in 
  let postfix = applylexingrule (regexp (String.concat "" ["("; format_symbols; "\\]"]), 
			       fun (s:string) -> String.sub s 1 (String.length s - 2)) in 
  let infix = applylexingrule (regexp (String.concat "" ["("; format_symbols; ")"]), 
			       fun (s:string) -> String.sub s 1 (String.length s - 2)) in 
  (* no fix *)
  tryrule (fun pb ->
    let () = whitespaces pb in
    let s = nofix pb in
    let () = whitespaces pb in
    Symbol (s, Nofix)
  )
  (* prefix *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let s = prefix pb in
    let () = whitespaces pb in
    (* we might have the priority *)
    match mayberule (fun pb -> 
      let () = word ":" pb in
      let () = whitespaces pb in
      let i = parseint pb in
      let () = whitespaces pb in
      i
    ) pb with
      | None -> Symbol (s, Prefix 0)
      | Some i -> Symbol (s, Prefix i)
  )
  (* infix *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let s = infix pb in
    let () = whitespaces pb in
    (* we might have the priority *)
    match mayberule (fun pb -> 
      let () = word ":" pb in
      let () = whitespaces pb in
      let a = parseassoc pb in
      let () = whitespaces pb in
      let () = word "," pb in
      let () = whitespaces pb in
      let i = parseint pb in
      let () = whitespaces pb in
      (a, i)
    ) pb with
      | None -> Symbol (s, Infix (0, NoAssoc))
      | Some (a, i) -> Symbol (s, Infix (i, a))	
  )
  (* postfix *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let s = postfix pb in
    let () = whitespaces pb in
    (* we might have the priority *)
    match mayberule (fun pb -> 
      let () = word ":" pb in
      let () = whitespaces pb in
      let i = parseint pb in
      let () = whitespaces pb in
      i
    ) pb with
      | None -> Symbol (s, Postfix 0)
      | Some i -> Symbol (s, Postfix i)
  )
  (* just a name *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let n = name_parser pb in
    let () = whitespaces pb in
    Name n
  )


let parse_symbol (defs: defs) : symbol parsingrule =
  fun pb -> 
    let res = fold_stop (fun () s ->
      try
	let () = tryrule (word (symbol2string s)) pb in
	Right s
      with
	| NoMatch -> Left ()
    ) () (List.flatten defs.hist) in
    match res with
      | Left () -> raise NoMatch
      | Right s -> s
	

let create_opparser_term (defs: defs) (primary: term parsingrule) : term opparser =
  let res = { primary = primary;
	      prefixes = Hashtbl.create (List.length defs.hist);
	      infixes = Hashtbl.create (List.length defs.hist);
	      postfixes = Hashtbl.create (List.length defs.hist);
	      reserved = parse_reserved;
	    } in
  let _ = List.map (fun s -> 
    match s with
      | Name _ -> ()
      | Symbol (n, Nofix) -> ()
      | Symbol (n, Prefix i) -> Hashtbl.add res.prefixes n (i, fun pos te -> App (Cste (s, pos), [te, Explicit], (fst pos, snd (get_term_pos te))))
      | Symbol (n, Infix (i, a)) -> Hashtbl.add res.infixes n (i, a, fun pos te1 te2 -> App (Cste (s, pos), [te1, Explicit; te2, Explicit], (fst (get_term_pos te1), snd (get_term_pos te2))))
      | Symbol (n, Postfix i) -> Hashtbl.add res.postfixes n (i, fun pos te -> App (Cste (s, pos), [te, Explicit], (fst (get_term_pos te), snd pos)))
  ) (List.flatten defs.hist) in
  res

let create_opparser_pattern (defs: defs) (primary: pattern parsingrule) : pattern opparser =
  let res = { primary = primary;
	      prefixes = Hashtbl.create (List.length defs.hist);
	      infixes = Hashtbl.create (List.length defs.hist);
	      postfixes = Hashtbl.create (List.length defs.hist);
	      reserved = parse_reserved;
	    } in
  let _ = List.map (fun s -> 
    match s with
      | Name _ -> ()
      | Symbol (n, Nofix) -> ()
      | Symbol (n, Prefix i) -> Hashtbl.add res.prefixes n (i, fun pos te -> PApp ((s, pos), [te, Explicit], AVar nopos, (fst pos, snd (get_pattern_pos te))))
      | Symbol (n, Infix (i, a)) -> Hashtbl.add res.infixes n (i, a, fun pos te1 te2 -> PApp ((s, pos), [te1, Explicit; te2, Explicit], AVar nopos, (fst (get_pattern_pos te1), snd (get_pattern_pos te2))))
      | Symbol (n, Postfix i) -> Hashtbl.add res.postfixes n (i, fun pos te -> PApp ((s, pos), [te, Explicit], AVar nopos, (fst (get_pattern_pos te), snd pos)))
  ) (List.flatten defs.hist) in
  res

(* these are the whole term set 
   - term_lvlx "->" term
*)
let rec parse_term (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  tryrule (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let (names, ty, nature) = parse_impl_lhs defs leftmost pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "->") pb in
    let () = whitespaces pb in
    let body = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    set_term_pos (build_impl names ty nature body) (startpos, endpos)
  ) 
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let () = at_start_pos leftmost (word "\\") pb in
    let () = whitespaces pb in
    let qs = many1 (parse_lambda_lhs defs leftmost) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "->") pb in
    let () = whitespaces pb in
    let body = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    set_term_pos (build_lambdas qs body) (startpos, endpos)
  ) 
  <|> parse_term_lvl0 defs leftmost
end pb

and parse_impl_lhs (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : ((symbol * pos) list * term * nature) = begin
  (* first case 
     with paren
  *)
  tryrule (paren (fun pb ->
    let names = many1 (fun pb ->
      let () = whitespaces pb in
      let startpos = cur_pos pb in
      let n = at_start_pos leftmost name_parser pb in
      let endpos = cur_pos pb in
      let () = whitespaces pb in
      n, (startpos, endpos)
    ) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "::") pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    (List.map (fun (n, p) -> Name n, p) names, ty, Explicit)
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let names = many1 (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let n = at_start_pos leftmost name_parser pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    n, (startpos, endpos)
    ) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "::") pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    (List.map (fun (n, p) -> Name n, p) names, ty, Implicit)
  )
  )
  (* or just a type -> anonymous arguments *)
  <|> (fun pb -> 
    let ty = parse_term_lvl0 defs leftmost pb in
    ([Symbol ("_", Nofix), nopos], ty, Explicit)        
  )
  <|> (fun pb -> 
    let () = whitespaces pb in
    let ty = at_start_pos leftmost (paren (parse_term_lvl0 defs leftmost)) pb in
    ([Symbol ("_", Nofix), nopos], ty, Explicit)        
  )
  <|> (fun pb -> 
    let () = whitespaces pb in
    let ty = at_start_pos leftmost (bracket (parse_term_lvl0 defs leftmost)) pb in
    ([Symbol ("_", Nofix), nopos], ty, Implicit)        
  )
end pb

and parse_lambda_lhs (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : ((symbol * pos) list * term * nature) = begin
  (* first case 
     with paren
  *)
  tryrule (paren (fun pb ->
    let names = many1 (fun pb ->
      let () = whitespaces pb in
      let startpos = cur_pos pb in
      let n = at_start_pos leftmost name_parser pb in
      let endpos = cur_pos pb in
      let () = whitespaces pb in
      n, (startpos, endpos)
    ) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "::") pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    (List.map (fun (n, p) -> Name n, p) names, ty, Explicit)
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let names = many1 (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let n = at_start_pos leftmost name_parser pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    n, (startpos, endpos)
    ) pb in
    let ty = match (mayberule (fun pb ->
      let () = whitespaces pb in
      let () = at_start_pos leftmost (word "::") pb in
      let () = whitespaces pb in
      let ty = parse_term defs leftmost pb in
      ty
    ) pb) with
      | None -> AVar nopos
      | Some ty -> ty in
    (List.map (fun (n, p) -> Name n, p) names, ty, Implicit)
  )
  )
  <|> (fun pb -> 
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let n = at_start_pos leftmost name_parser pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    ([Name n, (startpos, endpos)], AVar nopos, Explicit)        
  )

end pb

(* this is operator-ed terms with term_lvl1 as primary
*)
and parse_term_lvl0 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  let myp = create_opparser_term defs (parse_term_lvl1 defs leftmost) in
  opparse myp
end pb

(* this is term resulting for the application of term_lvl2 *)
and parse_term_lvl1 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  fun pb -> 
    (* first we parse the application head *)
    let startpos = cur_pos pb in
    let head = parse_term_lvl2 defs leftmost pb in    
    let () = whitespaces pb in
    (* then we parse the arguments *)
    let args = separatedBy (
      fun pb ->
	parse_arguments defs leftmost pb
    ) whitespaces pb in
    let endpos = cur_pos pb in
    match args with
      | [] -> head
      | _ -> 
	App (head, args, (startpos, endpos))
end pb

(* arguments: term_lvl2 with possibly brackets *)
and parse_arguments (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : (term * nature) = begin
  (fun pb -> 
    let () = whitespaces pb in
    let te = at_start_pos leftmost (bracket (parse_term_lvl2 defs leftmost)) pb in
    (te, Implicit)
  )
  <|> (fun pb -> 
    let te = parse_term_lvl2 defs leftmost pb in
    (te, Explicit)
  )
end pb

(* these are the most basic terms + top-level terms in parenthesis *)
and parse_term_lvl2 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  tryrule (fun pb -> 
    let () = whitespaces pb in
    let (), pos = at_start_pos leftmost (with_pos (word "Type")) pb in
    let () = whitespaces pb in
    Type pos
  ) 
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let (), pos = at_start_pos leftmost (with_pos parse_avar) pb in
    let () =  whitespaces pb in
    AVar pos
  ) 
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let startpos = cur_pos pb in    
    let () = at_start_pos leftmost (word "match") pb in
    let () =  whitespaces pb in
    let te = parse_term defs leftmost pb in
    let () =  whitespaces pb in
    let () = at_start_pos leftmost (word "with") pb in
    let eqs = many (fun pb ->
      let () = whitespaces pb in
      let () = at_start_pos leftmost (word "|") pb in
      let () = whitespaces pb in
      let p = at_start_pos leftmost (parse_pattern defs leftmost) pb in
      let () = whitespaces pb in
      let () = at_start_pos leftmost (word ":=") pb in
      let startpos = cur_pos pb in
      let () = whitespaces pb in
      let te = parse_term defs startpos pb in
      p, te
    ) pb in
    let endpos = cur_pos pb in    
    Match (te, eqs, (startpos, endpos))
  )
  <|> tryrule (fun pb -> 
    let () = whitespaces pb in
    let s, pos = at_start_pos leftmost (with_pos (parse_symbol_name defs)) pb in
    let () =  whitespaces pb in    
    TName (s, pos)
  )
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let n, pos = at_start_pos leftmost (with_pos name_parser) pb in
    let () = whitespaces pb in
    TName (Name n, pos)
  )
  <|> (fun pb -> 
    let () = whitespaces pb in
    at_start_pos leftmost (paren (parse_term defs leftmost)) pb)
end pb

and parse_pattern (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : pattern = begin
  let myp = create_opparser_pattern defs (parse_pattern_lvl1 defs leftmost) in
  opparse myp
end pb

and parse_pattern_lvl1 (defs: defs) (leftmost: (int * int)) : pattern parsingrule =
  tryrule (fun pb -> 
    (* first we parse the application head *)
    let () = whitespaces pb in
    let s, pos = at_start_pos leftmost (with_pos (parse_symbol defs)) pb in    
    let () = whitespaces pb in
    (* then we parse the arguments *)
    let args = List.flatten (
      separatedBy (
	fun pb ->
	  parse_pattern_arguments defs leftmost pb
      ) whitespaces pb) in
    let endpos = cur_pos pb in
    match args with
      | [] -> PCste (s, pos)
      | _ -> PApp ((s, pos), args, AVar nopos, (fst pos, endpos))	  
  )
  <|> tryrule (parse_pattern_lvl2 defs leftmost)


and parse_pattern_arguments (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : (pattern * nature) list = begin
  tryrule (paren (fun pb ->
    let patterns = many1 (fun pb ->
      let () = whitespaces pb in
      let n = parse_pattern_lvl2 defs leftmost pb in
      let () = whitespaces pb in
      n
    ) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "::") pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    List.map (fun p -> set_pattern_type p ty, Explicit) patterns
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let patterns = many1 (fun pb ->
    let () = whitespaces pb in
    let n =  parse_pattern_lvl2 defs leftmost pb in
    let () = whitespaces pb in
    n
    ) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "::") pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    List.map (fun p -> set_pattern_type p ty, Implicit) patterns
  )
  )
  <|>(fun pb -> 
    let () = whitespaces pb in
    let te = at_start_pos leftmost (bracket (parse_pattern defs leftmost)) pb in
    [te, Implicit]
  )
  <|>(fun pb -> 
    let () = whitespaces pb in
    let te = at_start_pos leftmost (paren (parse_pattern defs leftmost)) pb in
    [te, Explicit]
  )
  <|> (fun pb -> 
    let te = parse_pattern_lvl2 defs leftmost pb in
    [te, Explicit]
  )
end pb
  
and parse_pattern_lvl2 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : pattern = begin
  tryrule (fun pb -> 
    let () = whitespaces pb in
    let (), pos = at_start_pos leftmost (with_pos (word "Type")) pb in
    let () = whitespaces pb in
    PType pos
  ) 
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let (), pos = at_start_pos leftmost (with_pos parse_avar) pb in
    let () =  whitespaces pb in
    PAVar (AVar nopos, pos) 
  ) 
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let s, pos = at_start_pos leftmost (with_pos (parse_symbol defs)) pb in
    let () =  whitespaces pb in
    PCste (s, pos)
  )
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let startpos = cur_pos pb in
    let name = at_start_pos leftmost name_parser pb in
    let () = at_start_pos leftmost (word "@") pb in
    let p = parse_pattern defs leftmost pb in
    let endpos = cur_pos pb in
    PAlias (name, p, AVar nopos, (startpos, endpos))
  )
  <|> tryrule (fun pb -> 
    let () =  whitespaces pb in
    let name, pos = at_start_pos leftmost (with_pos name_parser) pb in
    let () =  whitespaces pb in    
    PVar (name, AVar nopos, pos)
  )
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in    
    at_start_pos leftmost (paren (parse_pattern defs leftmost)) pb    
  )
end pb

type definition = DefSignature of symbol * term
		  | DefEquation of pattern * term
		  | DefTerm of term
		  | DefInductive of symbol * ((symbol * pos) list * term * nature) list * term * (symbol * term) list
		  (* the following constructors are not language element per say, but commands *)
		  | Load of string

let rec parse_definition (defs: defs) (leftmost: int * int) : definition parsingrule =
  (* here we first try to parse command:
     - Load <filename>
  *)
  tryrule (fun pb ->
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "Load") pb in
    let () = whitespaces pb in
    let filename = at_start_pos leftmost name_parser pb in
    let () = whitespaces pb in
    Load filename
  )
  (* then we try to parse basic definitions: 
     - Inductive types
     - Signature
     - Equation
     - Term
  *)
  (* an inductive *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let s = at_start_pos leftmost (parse_symbol_name_def) pb in
    let () = whitespaces pb in
    let args = many (parse_lambda_lhs defs leftmost) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "::") pb in
    let startpos = cur_pos pb in
    let () = whitespaces pb in
    let ty = parse_term defs startpos pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":=") pb in
    let () = whitespaces pb in
    (* we need to create a copy of the definition, in order to parse the Inductive type symbol *)
    let defs = { defs with hist = [s]::defs.hist } in
    let constrs = many (fun pb ->
      let () = whitespaces pb in
      let () = at_start_pos leftmost (word "|") pb in
      let () = whitespaces pb in
      let s = at_start_pos leftmost (parse_symbol_name_def) pb in
      let () = whitespaces pb in
      let () = at_start_pos leftmost (word "::") pb in
      let startpos = cur_pos pb in
      let () = whitespaces pb in
      let ty = parse_term defs startpos pb in
      s, ty
    ) pb in
    DefInductive (s, args, ty, constrs)
  )
  (* a signature *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let s = at_start_pos leftmost (parse_symbol_name_def) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word "::") pb in
    let startpos = cur_pos pb in
    let () = whitespaces pb in
    let ty = parse_term defs startpos pb in
    DefSignature (s, ty)
  )
  (* here we should have the Destructor parser *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let p = at_start_pos leftmost (parse_pattern defs leftmost) pb in
    let () = whitespaces pb in
    let () = at_start_pos leftmost (word ":=") pb in
    let startpos = cur_pos pb in
    let () = whitespaces pb in
    let te = parse_term defs startpos pb in
    DefEquation (p, te)
  )
  (* finally a free term *)
  <|> tryrule (fun pb ->
    DefTerm (parse_term defs leftmost pb)
  )

let parse_onedefinition defs : (int * definition) parsingrule = 
  fun pb -> 
    let posstart = pb.beginpointer in
    let () = whitespaces pb in
    let leftmost = cur_pos pb in
    let def = parse_definition defs leftmost pb in
    let () = whitespaces pb in
    let posend = pb.beginpointer in  
    posend - posstart - 1, def
