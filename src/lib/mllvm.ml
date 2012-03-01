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
		| TCste of lltype
		| TName of string

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
		      | TFunction of (string * llvmtype) array * llvmtype * bool
		      | TPointer of llvmtype


(* some shortcut functions *)
let uinteger = fun i -> TPrimitive (TIntegerType (TUInteger i));;
let sinteger = fun i -> TPrimitive (TIntegerType (TSInteger i));;
let double_ = TPrimitive (TFloatingType TDouble);;
let float_ = TPrimitive (TFloatingType TFloat);;
let quad = TPrimitive (TFloatingType TQuad);;
let struct_ = fun tys -> TDerived (TAggregate (TStructure tys));;
let pstruct_ = fun tys -> TDerived (TAggregate (TPackedStructure tys));;
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


type typestore = (string, (llvmtype * lltype)) Hashtbl.t
;;

let rec llvmtype2lltype (ty: llvmtype) (tyst: typestore) (ctxt: llcontext) : lltype =
  match ty with
    | TPrimitive tp -> llvmprimitivetype2lltype tp ctxt      
    | TDerived td -> llvmderivedtype2lltype td tyst ctxt
    | TName n -> snd 
      (try 
	 Hashtbl.find tyst n
       with
	 | e -> 
	   printf "cannot find %s:\n" n; flush stdout;
	   raise e
      )
    | TCste c -> c

and llvmprimitivetype2lltype (ty: llvmprimitivetype) (ctxt: llcontext) : lltype =
  match ty with
    | TVoid -> void_type ctxt
    | TLabel -> label_type ctxt
    | TLabelPtr -> pointer_type (label_type ctxt)
    | TIntegerType ti -> llvmintegertype2lltype ti ctxt
    | TFloatingType tf -> llvmfloatingtype2lltype tf ctxt

and llvmintegertype2lltype (ty: llvmintegertype) (ctxt: llcontext) : lltype =
  match ty with
    | TUInteger i | TSInteger i -> integer_type ctxt i

and llvmfloatingtype2lltype (ty: llvmfloatingtype) (ctxt: llcontext) : lltype =
  match ty with
    | TFloat -> float_type ctxt
    | TDouble -> double_type ctxt
    | TQuad -> fp128_type ctxt

and llvmderivedtype2lltype (ty: llvmderivedtype) (tyst: typestore) (ctxt: llcontext) : lltype =
  match ty with
    | TAggregate tag -> llvmaggregatetype2lltype tag tyst ctxt
    | TFunction (args, retty, varargs) ->  
      let retty = llvmtype2lltype retty tyst ctxt in
      let args = Array.map (fun (_, ty) -> llvmtype2lltype ty tyst ctxt) args in
      (if varargs then var_arg_function_type else function_type) retty args
    | TPointer ty -> pointer_type (llvmtype2lltype ty tyst ctxt)

and llvmaggregatetype2lltype (ty: llvmaggregatetype) (tyst: typestore) (ctxt: llcontext) : lltype =
  match ty with
    | TArray (i, ty) -> array_type (llvmtype2lltype ty tyst ctxt) i
    | TStructure ls -> struct_type ctxt (Array.map (fun (_, ty) -> llvmtype2lltype ty tyst ctxt) ls)
    | TPackedStructure ls -> packed_struct_type ctxt (Array.map (fun (_, ty) -> llvmtype2lltype ty tyst ctxt) ls)
    | TVector (i, Left ti) -> vector_type (llvmintegertype2lltype ti ctxt) i
    | TVector (i, Right tf) -> vector_type (llvmfloatingtype2lltype tf ctxt) i

;;

let rec define_llvmtype (l: (string * llvmtype) array) (tyst: typestore) (ctxt: llcontext) : unit =
  (* 
     first we insert in the typestore the structured (the only possible recursive types)
  *)
  let () = Array.iter (fun (name, def) -> 
      match def with
	| TDerived (TAggregate (TStructure _)) | TDerived (TAggregate (TPackedStructure _)) ->
	  let structty = named_struct_type ctxt name in
	  printf "%s := %s\n" name (string_of_lltype structty); flush stdout;
	  Hashtbl.add tyst name (def, structty)
	| _ -> ()
  ) l in
  printf "define_llvmtype (1)\n"; flush stdout;
  (* then we compute all the types except the structures *)
  let () = Array.iter (fun (name, def) -> 
      match def with
	| TDerived (TAggregate (TStructure _)) | TDerived (TAggregate (TPackedStructure _)) ->
	  ()
	| _ -> 
	  let ty = llvmtype2lltype def tyst ctxt in
	  printf "%s := %s\n" name (string_of_lltype ty); flush stdout
  ) l in
  printf "define_llvmtype (2)\n"; flush stdout;

  (* finally we set the structure bodies *)
  let () = Array.iter (fun (name, def) -> 
      match def with
	| TDerived (TAggregate (TStructure elts)) ->
	  let structty = snd (Hashtbl.find tyst name) in
	  struct_set_body structty (Array.map (fun (_, ty) -> llvmtype2lltype ty tyst ctxt) elts) false
	  
	| TDerived (TAggregate (TPackedStructure elts)) ->
	  let structty = snd (Hashtbl.find tyst name) in
	  struct_set_body structty (Array.map (fun (_, ty) -> llvmtype2lltype ty tyst ctxt) elts) true
	| _ -> 
	  ()
  ) l in
  printf "define_llvmtype (3)\n"; flush stdout;
  ()
;;  

(* *)
type llvmvalue = llvalue * llvmtype;;

let null (ty: llvmtype) (tyst: typestore) (ctxt: llcontext) : llvmvalue = (const_null (llvmtype2lltype ty tyst ctxt), ty) ;;

(*
Definitions
*)
type llvmdef = TypeDef of (string * llvmtype) array
	       | SignatureDef of string * (string * llvmtype) array * llvmtype * bool
	       | GlobalDef of string * (llvmtype, llvmvalue) either
;;

type valuestore = (string, llvmvalue) Hashtbl.t;;

(*
val module_context : llmodule -> llcontext
*)
let llvmdef_proceed 
    (def: llvmdef) 
    (tyst: typestore) 
    (vst: valuestore)
    (modul: llmodule)
    : unit =
  match def with
    | TypeDef typs -> 
      define_llvmtype typs tyst (module_context modul)
    | SignatureDef (n, args, retty, varargs) -> 
      let fctty = function_ args retty varargs in
      let ctxt = module_context modul in
      let fct = declare_function n (llvmtype2lltype fctty tyst ctxt) modul in      
      Hashtbl.add vst n (fct, fctty)
    | GlobalDef (n, Left ty) ->
      let ctxt = module_context modul in
      let g = declare_global (llvmtype2lltype ty tyst ctxt) n modul in
      Hashtbl.add vst n (g, ty);
    | GlobalDef (n, Right (v, ty)) ->
      let g = define_global n v modul in
      Hashtbl.add vst n (g, ty)

;;


(*
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

type blockstore = (string, llbasicblock) Hashtbl.t
;;

let llvmexpr_semantics (builder: llbuilder) (tyst: typestore) (vst: valuestore) (bst: blockstore) : unit =
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
;;

*)
