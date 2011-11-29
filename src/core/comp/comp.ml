open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;

open Printf;;

(********************* general LLVM setup ********************)

ignore (initialize_native_target ());;

let context = global_context ();;

let modul = create_module context "mymms";;

let engine = ExecutionEngine.create modul;;

let pass_manager = PassManager.create_function modul;;

let target_data = ExecutionEngine.target_data engine;;

printf "target_data := %s\n" (TargetData.as_string target_data);;

TargetData.add target_data pass_manager;;

(* optimizations *)

add_constant_propagation pass_manager;
add_sccp pass_manager;
add_dead_store_elimination pass_manager;
add_aggressive_dce pass_manager;
add_scalar_repl_aggregation pass_manager;
add_ind_var_simplification pass_manager;    
add_instruction_combination pass_manager;
add_licm pass_manager;
(*add_loop_unswitch pass_manager;*)
add_loop_unroll pass_manager;
add_loop_rotation pass_manager;
(*add_loop_index_split pass_manager;*)
add_memory_to_register_promotion pass_manager;
add_memory_to_register_demotion pass_manager;
add_reassociation pass_manager;
add_jump_threading pass_manager;
add_cfg_simplification pass_manager;
add_tail_call_elimination pass_manager;
add_gvn pass_manager;
add_memcpy_opt pass_manager;
add_loop_deletion pass_manager;
add_lib_call_simplification pass_manager;

(* init passmanager *)
ignore (PassManager.initialize pass_manager);;


(*
  here we should define prototype of some useful functions
  - malloc
  - free
  - memcpy
  - ...
*)

(******************* value encoding **********************)

(* some redefinition *)

let i8_type : lltype = i8_type context;;

let ptri8_type : lltype = pointer_type i8_type;;

(* the type of a value ( := int _) and of its (pointer (int _)) *)
(* value_ty_size >= ptrvalue_ty 
   if = then we can use directly build_ptrtoint/build_inttoptr
   else we need to use build_zext/build_trunc

   rmq: here we are taking the same size, but for some case, one might want to use different size (to avoid boxing)
*)

(* := int _ *)
let value_ty : lltype = intptr_type target_data;;
let value_ty_size : int = Int64.to_int (size_in_bits target_data value_ty);;
let value_align : int = abi_align target_data value_ty;;

printf "value: ty := %s; size := %d; align := %d\n" (string_of_lltype value_ty) value_ty_size value_align;;

(* := ptr (int _) *)
let ptrvalue_ty : lltype = pointer_type value_ty;;
let ptrvalue_ty_size : int = Int64.to_int (size_in_bits target_data ptrvalue_ty);;
let ptrvalue_align : int = abi_align target_data ptrvalue_ty;;

printf "ptrvalue: ty := %s; size := %d; align := %d\n" (string_of_lltype ptrvalue_ty) ptrvalue_ty_size ptrvalue_align;;

(* we can compute the number of less-significant bits irrelevant in a ptr *)
let free_bits : int = int_of_float (log (float (min value_align ptrvalue_align)) /. log 2.);;

printf "free_bits := %d\n" free_bits;;

(* make sure we have at least 2 bits *)
assert (free_bits >= 2);;

(* this number of bits will be use to mark two things
   bit 0 -> if 1 we are sure that the value encode a cste value (rather than a pointer to a applied value)
   bit 1 -> if == 1 then the value is an axiom | constructor id 
         -> if == 0 then the value is a (llvm) function pointer
 *)

(* the empty value and error value*)
let empty_value : llvalue = const_all_ones value_ty;;
let error_value : llvalue = const_null value_ty;;

(* a simple test *)

(* *)

(******************* GC related Code **********************)



(******************* mymms Compiler **********************)

