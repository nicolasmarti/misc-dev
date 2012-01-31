open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;

open Printf;;

open Map;;
open Set;;

type var = string;;

module OrderedVar = 
    struct
      type t = var
      let compare x y = String.compare x y
    end;;

module VarSet = Set.Make(OrderedVar);; 

module VarMap = Map.Make(OrderedVar);; 

type ('a, 'b) either = Left of 'a
		       | Right of 'b
;;

(* the llvm types *)

type llvmtype = TPrimitive of llvmprimitivetype
		| TDerived of llvmderivedtype
		| TCste of string

and llvmprimitivetype = TLabel
			| TLabelPtr
			| TIntegerType of llvmintegertype
			| TFloatingType of llvmfloatingtype
			| TVoid

and llvmintegertype = TUInteger of int
		      | TSInteger of int

and llvmfloatingtype = TFloat
		       | TDouble
		       | TQuad

and llvmaggregatetype = TArray of int * llvmtype
			| TStructure of (string * llvmtype) array
			| TPackedStructure of (string * llvmtype) array
			| TVector of int * (llvmintegertype, llvmfloatingtype) either
			    
and llvmderivedtype = TAggregate of llvmaggregatetype
		      | TFunction of llvmtype array * llvmtype * bool
		      | TPointer of llvmtype


(* some shortcut functions *)
let uinteger = fun i -> TPrimitive (TIntegerType (TUInteger i));;
let sinteger = fun i -> TPrimitive (TIntegerType (TSInteger i));;
let double = TPrimitive (TFloatingType TDouble);;
let float = TPrimitive (TFloatingType TFloat);;
let quad = TPrimitive (TFloatingType TQuad);;
let struct_ = fun tys -> TDerived (TAggregate (TStructure tys));;
let array = fun ty sz -> TDerived (TAggregate (TArray (sz, ty)));;
let vector = fun ty sz ->
  match ty with
    | TPrimitive (TIntegerType i) -> TDerived (TAggregate (TVector (sz, Left i)))
    | TPrimitive (TFloatingType f) -> TDerived (TAggregate (TVector (sz, Right f)))
    | _ -> raise (Failure "vector: only vector of integer or floating are valid")
;;
let void = TPrimitive TVoid;;
let function_ = fun tys ty is_var_arg ->
  TDerived (TFunction (tys, ty, is_var_arg))
;;
let pointer = fun ty -> TDerived (TPointer ty);;


type typestore = (string, llvmtype) Hashtbl.t
;;

let llvmtype2lltype (ty: llvmtype) (tyst: typestore) : lltype =
  raise (Failure "llvmtype2lltype: not yet implemented")
;;

(* *)
type llvmvalue = llvalue * llvmtype
;;

(* deep encoding of llvm expr, cmd, ... *)

type blockname = string;;

type unaryop = Not;;

type binaryop = Add | Sub | Mul | Div | Rem
		| Shl | LShl | AShl | And | Or | Xor;;

type compop = Eq | Ne | Lt | Gt | Le | Ge;;

type vectorop = ExtractElement of llvmexpr * llvmexpr 
		| InsertElement of llvmexpr * llvmexpr * llvmexpr 
		| ShuffleElement of llvmexpr * llvmexpr * llvmexpr
		    
and aggregateop = ExtractValue of llvmexpr  * int array
		  | InsertValue of llvmexpr * llvmexpr * int array		       
		      
and memaccessop = Alloca of llvmtype * llvmexpr option
		  | Load of llvmexpr
		  | Getelementptr of llvmexpr * llvmexpr array

and convop = ITrunc of llvmexpr * llvmtype
	     | IExt of llvmexpr * llvmtype
	     | FTrunc of llvmexpr * llvmtype
	     | FExt of llvmexpr * llvmtype
	     | F2I of llvmexpr * llvmtype
	     | I2F of llvmexpr * llvmtype
	     | I2Ptr of llvmexpr * llvmtype
	     | Ptr2I of llvmexpr * llvmtype
	     | BitCast of llvmexpr * llvmtype

and advancedop = ArrayLookup of llvmexpr * llvmexpr
		 | StructLookup of llvmexpr * string

and llvmexpr = UnaryOp of unaryop * llvmexpr
	       | BinaryOp of binaryop * llvmexpr * llvmexpr
	       | Vectorop of vectorop
	       | Memaccessop of memaccessop
	       | Convop of convop
	       | True | False | Compop of compop * llvmexpr * llvmexpr
	       | Call of llvmexpr * llvmexpr array
	       | Select of llvmexpr * llvmexpr * llvmexpr
	       | Var of var
	       | Cste of llvmvalue

	       | AdvancedOp of advancedop
;;

type varstore = (string, llvmvalue) Hashtbl.t
;;

type blockstore = (string, llbasicblock) Hashtbl.t
;;

let llvmexpr_semantics (builder: llbuilder) (tyst: typestore) (vst: varstore) (bst: blockstore) : unit =
  raise (Failure "llvmexpr_semantics: not yet implemented")
;;


(* command *)

type llvmassign = Store of llvmexpr * llvmexpr
		  | Let of var * llvmexpr

type llvmterminator = ReturnVoid
		      | Return of llvmexpr
		      | CondBr of llvmexpr * blockname * blockname
		      | Br of blockname
		      | Switch of llvmexpr * blockname * (llvmexpr * blockname) array
;;

type llvmcmd = Assign of llvmassign
	       | Terminator of llvmterminator
	       | Phi of var * (llvmexpr * blockname) array
;;

(* blocks *)
type llvmblock = {
  name: blockname;
  code: llvmcmd array;
};;

(* more abstract language *)
type cmd = CAssign of llvmassign 
	   | Ifte of cmd * cmd * cmd 
	   | Ift of cmd * cmd 
	   | Loop of cmd * cmd * cmd * bool
	   | Return of llvmexpr 

(* directive *)
type name = string;;


(*
'code can be 
* llvmblock array
* cmd

*)
type 'code llvmdirective = Type of (name * llvmtype) array
			   | Signature of name * llvmtype
			   | FunctionImplem of name * (name * llvmtype) array * 'code
			   | GlobalVar of name * llvmtype * llvmexpr
			   | GlobalCste of name * llvmtype * llvmexpr
;;

let llvmcmd_semantics (builder: llbuilder) (tyst: typestore) (vst: varstore) (bst: blockstore) : unit =
  raise (Failure "llvmcmd_semantics: not yet implemented")
;;