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
  - memalign
  Function: void * memalign (size_t boundary, size_t size)
  The memalign function allocates a block of size bytes whose address is a multiple of boundary. The boundary must be a power of two! The function memalign works by allocating a somewhat larger block, and then returning an address within the block that is on the specified boundary.
*)

(******************* value encoding **********************)

(* some redefinition *)

let i8_type : lltype = i8_type context;;

let i32_type : lltype = i32_type context;;

let ptri8_type : lltype = pointer_type i8_type;;

let size_type : lltype = integer_type context (Int64.to_int (size_in_bits target_data ptri8_type));;

let void_type : lltype = void_type context;;

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

flush stdout;;

(* make sure we have at least 2 bits *)
assert (free_bits >= 2);;

(* this number of bits will be use to mark two things
   bit 0 -> if 1 we are sure that the value encode a cste value (rather than a pointer to a applied value)
   bit 1 -> if == 1 then the value is an axiom | constructor | Inductive id  
         -> if == 0 then the value is a function (a (llvm) function pointer)
 *)

(* the empty value and error value*)
let empty_value : llvalue = const_all_ones value_ty;;
let error_value : llvalue = const_null value_ty;;

(* the semantics of value is the following
   (this semantics is only valid for "pure" terms (no Obj term that has a special compilation))
   * value:
   - if all the bit of the value are set: error value
   - if all the bit of the value are unset: this is an empty value
   - if the lesser bits of the value are 0x01: the upper bits are an (axiom | constructor | inductive | Type) id
   - if the lesser bits of the value are 0x11: the value with the lesser bits sets to 0x00 is a pointer of an llvm function
   - if the lesser bits of the value are 0x00: the value is a pointer to an application value (allocated in the GC)
   - if the lesser bits of the value are 0x10: ??????

   * application value:
   - a value corresponding to the head
   - a value, which semantics is a bitmap representing the arity + partially applied args
     0...01...10...0
     |-1-||-2-||-3-|
     1 -> partially applied args
     2 -> remaining args
     3 -> padded
     when all bits of bitmap are set to zero -> can be reduced (if head is a pointer to a llvm function -> give it the pointer to the args, replace the pointer to the application value, by the function returned value)
   - values of partially applied arguments

   It should works because we are eager
   
 *)

(* 


*)

(* utils *)

let log_i (x: int) (y: int) : int =
  let log_f = log (float x) /. log (float y) in
  let log_i = int_of_float log_f in
  if float log_i < log_f then log_i + 1 else log_i
;;

let div_i (x: int) (y: int) : int =
  let div_f = (float x) /. (float y) in
  let div_i = int_of_float div_f in
  if float div_i < div_f then div_i + 1 else div_i
;;

let rec power_i (x: int) (y: int) : int =
  if y = 0 then 1 else x * power_i x (y-1)
;;

(* some usefull functions *)
let malloc_type : lltype = function_type ptri8_type [| size_type |];;
let malloc_ptr : llvalue = declare_function "malloc" malloc_type modul;;

let free_type : lltype = function_type void_type [| ptri8_type |];;
let free_ptr : llvalue = declare_function "free" free_type modul;;

let memalign_type : lltype = function_type ptri8_type [| size_type; size_type |];;
let memalign_ptr : llvalue = declare_function "memalign" memalign_type modul;;

let printi_type : lltype = function_type void_type [| size_type |];;
let printi_ptr : llvalue = declare_function "printi" printi_type modul;;

let printp_type : lltype = function_type void_type [| ptri8_type |];;
let printp_ptr : llvalue = declare_function "printp" printp_type modul;;

let memset_type : lltype = function_type ptri8_type [| ptri8_type; size_type; size_type |];;
let memset_ptr : llvalue = declare_function "memset" memset_type modul;;


(******************* GC related Code **********************)


let segment_count_type (nbbulk: int) : lltype = integer_type context (log_i nbbulk 2);;

let segment_bulk_type (nbbulk: int) (value_per_bulk: int) : lltype = array_type (array_type value_ty value_per_bulk) nbbulk;;

let bitmap_unit_size : int = 32;;
let bitmap_unit_type : lltype = integer_type context bitmap_unit_size;;
let bitmap_depth (nbbulk: int) : int = log_i nbbulk bitmap_unit_size;;

let bitmap_unit_level_size (nbbulk: int) (level: int) : int = 
  let nb_level = bitmap_depth nbbulk in
  if level >= nb_level then raise (Failure "level overflow");
  if level < 0 then raise (Failure "level overflow");
  let n = ref level in
  let res = ref (div_i nbbulk bitmap_unit_size) in
  while !n != 0 do
    res := div_i !res bitmap_unit_size;
    n := !n - 1;      
  done;
  !res
;;
  
let bitmap_levels_size (nbbulk: int) : int array =
  let nb_level = bitmap_depth nbbulk in
  Array.init nb_level (fun i ->
    let sz = bitmap_unit_level_size nbbulk i in
    (*printf "|BM^%d| := %d\n" i sz; flush stdout;*)
    sz
  )
;;

let bitmap_type (nbbulk: int) : lltype =
  let a = bitmap_levels_size nbbulk in
  let a = Array.map (fun i -> array_type bitmap_unit_type i) a in
  struct_type context a
;;


let segment_type (nbbulk: int) (value_per_bulk: int) : lltype =
  let ty = struct_type context [| segment_count_type nbbulk; segment_bulk_type nbbulk value_per_bulk; bitmap_type nbbulk|] in
  (*printf "segment_type := %s\n" (string_of_lltype ty); flush stdout;*)
  ty
;;

let nb_lebel_to_nbbulk (level: int) = 
  power_i bitmap_unit_size level 
;;


let segment_alignment : llvalue =
  let nbbulk = nb_lebel_to_nbbulk 2 in
  printf "nbbulk = %d\n" nbbulk; flush stdout;
  let sum = ref 0 in
  let maxsz = ref 0 in
  let _ = Array.init (value_ty_size - 3) (fun i -> 
    let segment_ex_type = segment_type nbbulk (i+3) in
    let sz = Int64.to_int (size_in_bits target_data segment_ex_type) in
    let stsz = Int64.to_int (store_size target_data segment_ex_type) in
    let abisz = Int64.to_int (abi_size target_data segment_ex_type) in
    let abize_ko = div_i abisz 1024 in
    let segment_type_str = string_of_lltype segment_ex_type in
    printf "%d value bulks; type := %s; size := %d k.o.\n" (i + 3) segment_type_str abize_ko; flush stdout;
    sum := !sum + abize_ko;
    if !maxsz < abize_ko then maxsz := abize_ko
  ) in
  printf "total size <= %d k.o.\n" !sum; flush stdout;
  printf "max size := %d \n" !maxsz; flush stdout;
  let log2 = log_i (!maxsz * 1024) 2 in
  printf "alignment := %d k.o (2^%d) [padding = %d k.o.]\n" (div_i (power_i 2 log2) 1024) log2 (div_i ((power_i 2 log2) - (!maxsz * 1024)) 1024); flush stdout;
  printf "number of allocable segment := %d\n" (power_i 2 (32 - log2)); flush stdout;
  const_int size_type (power_i 2 log2)  
;;

(* build gc init function *)

let gc_init_type = function_type void_type [| void_type |];;

let gc_init_fct = declare_function "gc_init" gc_init_type modul;;

let _ = 
  let entryb = append_block context "entry" gc_init_fct in
  let builder = builder context in
  let _ = position_at_end entryb builder in

  let nbbulk = nb_lebel_to_nbbulk 2 in
  
  let _ = Array.init (value_ty_size - 3) (fun i -> 
    let segment_ex_type = segment_type nbbulk (i+3) in
    let segment_null = const_null segment_ex_type in
    let segment_size = Int64.to_int (store_size target_data segment_ex_type) in
    let segmentptr = build_call memalign_ptr [| segment_alignment; const_int size_type segment_size |] "segmentptr" builder in
    let _ = build_call memset_ptr [| segmentptr; const_int size_type 0; const_int size_type segment_size |] "memset" builder in
    let _ = build_call printi_ptr [| const_int size_type (i+3) |] "debug" builder in
    let _ = build_call printp_ptr [| segmentptr |] "debug" builder in
    ()
  ) in
  build_ret_void builder
;;

dump_module modul
;;

ignore(ExecutionEngine.run_function gc_init_fct [||] engine);;

(******************* mymms Compiler **********************)

