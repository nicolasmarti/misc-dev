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
  method virtual apply: 'c -> 'b -> ('a * nature) list -> 'a
end

type path

type level

type op = Nofix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int

type Sort = Set of level
	    | Prop of level
	    | Type of level

type term = TSort of Sort * pos
	    | Cste of path * name * pos * typeannotation

	    | BVar of index * pos * typeannotation
	    | FVar of index * pos * typeannotation
	    | PVar of name * pos * typeannotation

	    | Impl of (name * term * nature * pos) * term * pos * typeannotation
	    | Lambda of (name * term * nature * pos) * term * pos * typeannotation

	    | App of term * (term * nature) array * pos * typeannotation

	    | Match of term * (term array * term) array * pos * typeannotation

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
  (*role: role;*)
  pos: pos;
  
  fvs: (index * term * term * name option * pos option) list;
    
  termstack: term list;
  naturestack: nature list;
  patternstack: pattern list;
}

and definition = (name, (term * value)) Hashtbl.t
