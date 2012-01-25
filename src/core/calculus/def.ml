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

type op = Nofix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int

type symbol = | Name of name
	      | Symbol of name * op

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

type term = Type of pos
	    | Cste of symbol * pos
	    | Obj of (term, context, defs) tObj * pos

	    (* variables, >= 0 -> bounded variables, < 0 -> free variables *)
	    | TVar of index * pos
		
	    (* these constructors are only valide after parsing, and removed by typechecking *)
	    | AVar of pos
	    | TName of symbol * pos

	    (* quantifiers *)

	    | Impl of (symbol * term * nature * pos) * term * pos
	    | Lambda of (symbol * term * nature * pos) * term * pos

	    (* application *)

	    | App of term * (term * nature) list * pos

	    (* destruction *)
	    | Match of term * equation list * pos


(* N.B.: all types are properly scoped w.r.t. bounded var introduce by "preceding" pattern *)
and pattern = PType of pos 
	      | PVar of name * term * pos
	      | PAVar of term * pos
	      | PCste of symbol * pos
	      | PAlias of name * pattern * term * pos
	      | PApp of (symbol * pos) * (pattern * nature) list * term * pos

and equation = pattern * term

(* context of a term *)
(* N.B.: all terms are of the level in which they appear *)
and frame = {
  (* the symbol of the frame *)
  symbol : symbol;
  (* its type *)
  ty: term;
  (* the nature of the quantification *)
  nature: nature;
  (* its value: most stupid one: itself *)
  value: term;
  (* its position *)
  pos: pos;
    
  (* the free variables 
     - the index (redundant information put for sake of optimization)
     - the type of the free variable
     - its corresponding value (by unification)
  *)
  fvs: (index * term * term) list;

  (* the stacks *)
  termstack: term list;
  naturestack: nature list;
  patternstack: pattern list;
  
}

(* context *)
and context = frame list

and value = Inductive of symbol list
	    | Axiom
	    | Constructor
	    | Equation of equation list
	    | Primitive of (term, context, defs) tObj

(* definitions *)
and defs = {
  (* here we store all id in a string *)
  (* id -> (symbol * type * equations) *)
  store : (string, (symbol * term * value)) Hashtbl.t;
  hist : (symbol list) list;
}

let empty_frame = {
  symbol = Symbol ("_", Nofix);
  ty = Type nopos;
  nature = Explicit;
  value = TVar (0, nopos);
  pos = nopos;
  fvs = [];
  termstack = [];
  naturestack = [];
  patternstack = [];
}

type doudou_error = NegativeIndexBVar of index
		    | Unshiftable_term of term * int * int

		    | UnknownCste of symbol
		    | UnknownBVar of index * context
		    | UnknownFVar of index * context

		    | UnknownUnification of context * term * term
		    | NoUnification of context * term * term

		    | NoMatchingPattern of context * pattern * term

		    | PoppingNonEmptyFrame of frame

		    | CannotInfer of context * term * doudou_error
		    | CannotTypeCheck of context * term * term * term * doudou_error

		    | FreeError of string

exception DoudouException of doudou_error
