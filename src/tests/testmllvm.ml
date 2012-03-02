open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;

open Printf;;

open State;;

open Mllvm;;

open Hashtbl;;

let tyst : typestore = Hashtbl.create 100;;

let vst : valuestore = Hashtbl.create 100;;

let slist_ty (elt: llvmtype) : (string * llvmtype) =
  "slist", struct_ [| ("elt", elt) ; ("next", pointer (TName "slist")) |];;

let _ = llvmdef_proceed (TypeDef [| slist_ty void |]) tyst vst modul;;

let _ = llvmdef_proceed (GlobalDef ("g_slist", Left (TName "slist"))) tyst vst modul;;

let _ = llvmdef_proceed (GlobalDef ("empty_slist", Right (null (TName "slist") tyst context)))  tyst vst modul;;

let _ = llvmdef_proceed 
  (SignatureDef 
     ("app_list", 
      [| ("list1", TName "slist", [Attribute.Alignment 4]);
	 ("list2", TName "slist", [Attribute.Alignment 4])
      |],
      (void, [Attribute.Noinline]),
      false,
      (Some 71)
     )
  ) tyst vst modul;;

let _ = llvmexpr_cste (Var "empty_slist") tyst vst;;

let _ = dump_module modul;;
