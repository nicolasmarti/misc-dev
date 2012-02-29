open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;

open Printf;;

open State;;

open Mllvm;;

open Hashtbl;;

let tyst : typestore = Hashtbl.create 100;;

let slist_ty (elt: llvmtype) : (string * llvmtype) =
  "slist", struct_ [| ("elt", elt) ; ("next", pointer (TName "slist")) |];;

let slist = TName "slist";;

let _ = define_llvmtype [| slist_ty void |] tyst context;;

let _ = define_global "test_list" (const_null (llvmtype2lltype slist tyst context)) modul;;

let _ = printf "%s\n" (string_of_lltype (match type_by_name modul "slist" with | Some ty -> ty));;

let _ = dump_module modul;;
