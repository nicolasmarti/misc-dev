open Libparser
open Libpprinter

(*********************************)
(* Definitions of data structure *)
(*********************************)

type name = string

module NameMap = Map.Make(
  struct
    type t = string
    let compare x y = compare x y
  end
);;

module NameSet = Set.Make(
  struct
    type t = string
    let compare x y = compare x y
  end
);;

type index = int

module IndexSet = Set.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

module IndexMap = Map.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

type nature = Explicit
	      | Implicit

(* but in our case we only use 
   'a = term
   'b = context
   'c = defs
*)
class virtual ['a, 'b, 'c] tObj =
object 
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual pprint: unit -> token
  method virtual equal: ('a, 'b, 'c) tObj -> bool
  method virtual apply: 'c -> 'b -> ('a * nature) array -> 'a
end

type path = name list

type universe = int

type op = Nofix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int

type sort = Set of universe
	    | Prop of universe
	    | Type of universe

type term = TSort of sort * pos
	    | Cste of path * name * pos * typeannotation
	    | Obj of (term, context, definition) tObj * pos * typeannotation

	    | BVar of index * pos * typeannotation
	    | FVar of index * pos * typeannotation
	    | PVar of name * pos * typeannotation

	    | AVar of pos
	    | TName of path * name * pos

	    | Impl of (name * term * nature * pos) * term * pos * typeannotation
	    | Lambda of (name * term * nature * pos) * term * pos * typeannotation

	    | App of term * (term * nature) array * pos * typeannotation

	    | Destruct of term * (name * term) array * pos * typeannotation


and typeannotation = NoTypeAnnotation
		     | AnnotatedType of term
		     | InferedType of term
    
and value = Inductive of name array
	    | Constructor
	    | Axiom
	    | Equation of (term * name option * term) array
	    | Coercion
	    | Module of definition

and frame = {
  name: name;
  ty: term;
  nature: nature;

  pos: pos;
  
  fvs: (index * term * term * pos) list;
    
  termstack: term list;
  naturestack: nature list;
  patternstack: term list;

  known_unifications: (term * term) list
  
}

and context = frame list

and definition = {
  defs: (name, (term * value)) Hashtbl.t;
  notation: (name, name * op) Hashtbl.t;
  universe_strat: unit; (* TODO *)
}

type doudou_error = NegativeIndexBVar of index
		    | Unshiftable_term of term * int * int

		    | UnknownCste of path * name
		    | UnknownBVar of index * context
		    | UnknownFVar of index * context

		    | UnknownUnification of context * term * term
		    | NoUnification of context * term * term

		    | NoMatchingPattern of context * term * term

		    | PoppingNonEmptyFrame of frame

		    | CannotInfer of context * term * doudou_error
		    | CannotTypeCheck of context * term * term * term * doudou_error

		    | FreeError of string

exception DoudouException of doudou_error

let oracles_list : ((definition * context * term) -> term option) list ref = ref []

type debug_flags = {
  (* pretty printer flags *)
  mutable show_universe: bool;
  mutable show_implicit: bool;
  mutable show_varindices: bool;
  mutable show_position: bool;
  mutable show_proofs: bool;
}

let flags : debug_flags = {
  show_universe = true;
  show_implicit = true;
  show_varindices = true;
  show_position = true;
  show_proofs = true;
}
