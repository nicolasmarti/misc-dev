open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;

open Printf;;

let debug = ref false;;

(********************* general LLVM setup ********************)

ignore (initialize_native_target ());;

let optimize = ref false;;

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
add_loop_unroll pass_manager;
add_loop_rotation pass_manager;
add_memory_to_register_promotion pass_manager;
(*add_memory_to_register_demotion pass_manager;*)
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
let bool_type : lltype = i1_type context;;

let true_ : llvalue = const_int bool_type 1;;
let false_ : llvalue = const_int bool_type 0;;

let i8_type : lltype = i8_type context;;

let i32_type : lltype = i32_type context;;

let ptri8_type : lltype = pointer_type i8_type;;

let size_type_bits : int = Int64.to_int (size_in_bits target_data ptri8_type);;

let size_type : lltype = integer_type context size_type_bits;;

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

let prints_type : lltype = function_type void_type [| ptri8_type |];;
let prints_ptr : llvalue = declare_function "prints" prints_type modul;;


let llvm_printf str builder =
  let str = const_stringz context str in
  let alloca = build_alloca (type_of str) "alloca" builder in
  let _ = build_store str alloca builder in
  let alloca = build_bitcast alloca ptri8_type "alloca" builder in
  let _ = build_call prints_ptr [| alloca |] "" builder in
  ()
;;



(******************* GC related Code **********************)

(* the type of the counter of allocated bulk in the segment *)
let segment_count_type (nbbulk: int) : lltype = integer_type context (log_i nbbulk 2);;

(* the type of a bulk *)
let bulk_type (bulksize: int) : lltype = array_type value_ty bulksize;;

(* the type of the array of bulk *)
let segment_bulk_type (nbbulk: int) (bulksize: int) : lltype = array_type (bulk_type bulksize) nbbulk;;

(* a gc parameter: the number of bit per bitmap word *)
let bitmap_unit_size : int = 32;;
(* the type of bitmap word *)
let bitmap_unit_type : lltype = integer_type context bitmap_unit_size;;
(* the depth of the bitmap *)
let bitmap_depth (nbbulk: int) : int = log_i nbbulk bitmap_unit_size;;

(* the number of bitmap words per level *)
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

(* the last valid bitptr valid mask *)
let bimap_level_last_mask (nbbulk: int) (level: int) : int =
  let nb_level = bitmap_depth nbbulk in
  if level >= nb_level then raise (Failure "level overflow");
  if level < 0 then raise (Failure "level overflow");
  let nbelt = if level = 0 then nbbulk else bitmap_unit_level_size nbbulk (level - 1) in
  let divs = div_i nbelt bitmap_unit_size in
  let rest = divs * bitmap_unit_size - nbelt in
  bitmap_unit_size - rest - 1
;;

(* a bitptr is a pair of an index and a mask *)
let index_ty : lltype = bitmap_unit_type;;
let mask_ty : lltype = bitmap_unit_type;;

let max_mask_value : llvalue = const_shl (const_int bitmap_unit_type 1) (const_int (bitmap_unit_type) (bitmap_unit_size - 1));;
let min_mask_value : llvalue = const_int (bitmap_unit_type) 1;;

(* the type of the bitmap*)
let bitmap_levels_size (nbbulk: int) : int array =
  let nb_level = bitmap_depth nbbulk in
  Array.init nb_level (fun i ->
    let sz = bitmap_unit_level_size nbbulk i in
    (*printf "|BM^%d| := %d\n" i sz; flush stdout;*)
    sz
  )
;;

(* the type of the bitmap of a segment *)
let bitmap_type (nbbulk: int) : lltype =
  let a = bitmap_levels_size nbbulk in
  let a = Array.map (fun i -> array_type bitmap_unit_type i) a in
  struct_type context a
;;

let bitmap_size (nbbulk: int) : int =
  Int64.to_int (abi_size target_data (bitmap_type nbbulk));;

let segment_fct_ptr : lltype = 
  struct_type context [|
    pointer_type (function_type void_type [| ptri8_type |] ); (* mark_and_push *) 
    pointer_type (function_type void_type [| ptri8_type |]) (* clear *)
		       |]
;;

(* a segment type *)
let segment_type (nbbulk: int) (bulksize: int) : lltype =
  let ty = struct_type context [| 
    segment_fct_ptr;
    segment_count_type nbbulk; segment_bulk_type nbbulk bulksize; bitmap_type nbbulk|] in
  (*printf "segment_type := %s\n" (string_of_lltype ty); flush stdout;*)
  ty
;;

(* the type of the byteptr for a segment *)
let bitptr_type (nbbulk: int) : lltype = 
  array_type (struct_type context [| index_ty; mask_ty |]) (bitmap_depth nbbulk);;

(* the type of a bulk pointer *)
let bulkptr_type (bulksize: int) : lltype = pointer_type (bulk_type bulksize);; 

(* the type of an allocation pointer *)
let allocptr_type (nbbulk: int) (bulksize: int) : lltype = struct_type context [| pointer_type (segment_type nbbulk bulksize); bitptr_type nbbulk; bulkptr_type bulksize |];;

(* the size in bytes of a segments *)
let segment_size_bytes (nbbulk: int) (value_per_bulk: int) : int =
    let segment_ex_type = segment_type nbbulk value_per_bulk in
    Int64.to_int (abi_size target_data segment_ex_type)
;;

(* the max segment size: a power of two used for alignment *)
let max_segment_size_bit : int = 8;;
let max_segment_size : int = power_i 2 max_segment_size_bit
;;

(* given the max_segment_size, compute the number of bulk given their size *)
let nbbulk_from_bulksize (bulksize: int) : int =
  let sz = ref 1 in
  let loop = ref true in
  while !loop do
    if segment_size_bytes (!sz + 1) bulksize > max_segment_size then loop := false else sz := !sz + 1
  done;
  !sz
;;

(* we are going to build dynamically static functions in llvm *)

(* the global maxbitptr *)

let max_bitptr (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let var_name = String.concat "_" ["max_bitptr"; string_of_int bulksize; string_of_int level] in
  match lookup_global var_name modul with
    | Some v -> v
    | None ->
      let max_index = bitmap_unit_level_size nbbulk level - 1 in
      let max_mask = power_i 2 (bimap_level_last_mask nbbulk level) in
      let init = const_struct context [| const_int index_ty max_index; const_int mask_ty max_mask |] in
      define_global var_name init modul
;;


let one = const_int (integer_type context 32) 1;;
let zero = const_int (integer_type context 32) 0;;
let two = const_int (integer_type context 32) 2;;
let three = const_int (integer_type context 32) 3;;

(* 
   incBitPtr
 *)
let rec incBitPtr (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["incBitPtr"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->
      let fct_ty = function_type bool_type [|pointer_type (struct_type context [| index_ty; mask_ty |]) |] in
      let fct = declare_function fct_name fct_ty modul in
      let _ = set_value_name "bitptr" (params fct).(0) in
      let bitptr = (params fct).(0) in
      let max_bitptr = max_bitptr bulksize level in
      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let block1 = append_block context "indexeq_testmask" fct in
      let block2 = append_block context "indexeq_maskeq" fct in

      let block3 = append_block context "indexneq_testmask" fct in
      let block4 = append_block context "indexneq_maskeq" fct in
      let block5 = append_block context "indexneq_maskneq" fct in

      (* we first test that the bitptr is not maximal *)
      let indexptr = build_gep bitptr [| zero; zero |] "indexptr" builder in
      let index = build_load indexptr "index" builder in

      let maskptr = build_gep bitptr [| zero; one |] "maskptr" builder in
      let mask = build_load maskptr "mask" builder in

      let max_indexptr = build_gep max_bitptr [| zero; zero |] "max_indexptr" builder in
      let max_index = build_load max_indexptr "max_index" builder in

      let cmp = build_icmp Icmp.Eq index max_index "cmp" builder in 
      let _ = build_cond_br cmp block1 block3 builder in

      position_at_end block1 builder;
      
      let max_maskptr = build_gep max_bitptr [| zero; one |] "max_maskptr" builder in
      let max_mask = build_load max_maskptr "max_mask" builder in

      let cmp = build_icmp Icmp.Eq mask max_mask "cmp" builder in 
      let _ = build_cond_br cmp block2 block3 builder in

      position_at_end block2 builder;

      let _ = build_ret false_ builder in

      position_at_end block3 builder;

      let cmp = build_icmp Icmp.Eq mask max_mask_value "cmp" builder in 
      let _ = build_cond_br cmp block4 block5 builder in
      
      position_at_end block4 builder;
      
      let new_index = build_add index (const_int (type_of index) 1) "add" builder in
      let _ = build_store new_index indexptr builder in
      let _ = build_store min_mask_value maskptr builder in
      let _ = build_ret true_ builder in

      position_at_end block5 builder;

      let new_mask = build_shl mask (const_int (type_of index) 1) "shl" builder in
      let _ = build_store new_mask maskptr builder in
      let _ = build_ret true_ builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(* 
   indexToBitPtr
*)
let indexToBitPtr () : llvalue =
  let fct_name = String.concat "_" ["indexToBitPtr"] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->
      let fct_ty = function_type void_type [| pointer_type (struct_type context [| index_ty; mask_ty |]); index_ty |] in
      let fct = declare_function fct_name fct_ty modul in
      let _ = set_value_name "bitptr" (params fct).(0) in
      let bitptr = (params fct).(0) in
      let _ = set_value_name "index" (params fct).(1) in
      let index = (params fct).(1) in
      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let idx = build_udiv index (const_int (type_of index) bitmap_unit_size) "idx" builder in
      let rem = build_urem index (const_int (type_of index) bitmap_unit_size) "rem" builder in
      let mask = build_shl (const_int mask_ty 1) rem "mask" builder in

      let indexptr = build_gep bitptr [| zero; zero |] "indexptr" builder in
      let _ = build_store idx indexptr builder in

      let maskptr = build_gep bitptr [| zero; one |] "maskptr" builder in
      let _ = build_store mask maskptr builder in

      let _ = build_ret_void builder in
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(*
  log2
*)

let log2 () : llvalue =
  let fct_name = String.concat "_" ["log2"] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->
      let fct_ty = function_type index_ty [| mask_ty |] in
      let fct = declare_function fct_name fct_ty modul in
      let _ = set_value_name "n" (params fct).(0) in
      let n = (params fct).(0) in
      let entryb = append_block context "entry" fct in
      let exitb = append_block context "exit" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let resptr = build_alloca index_ty "resptr" builder in
      let _ = build_store (const_int index_ty 0) resptr builder in

      let nptr = build_alloca index_ty "nptr" builder in
      let _ = build_store n nptr builder in

      let sz = Int64.to_int (size_in_bits target_data mask_ty) in
      let log_ty = log_i sz 2 in
      assert (power_i 2 log_ty = sz);
      let blocks = Array.init log_ty (fun i ->
	append_block context "casetrue" fct, append_block context "next" fct
      ) in
      let _ = build_br (snd blocks.(0)) builder in      
      let _ = Array.init log_ty (fun i ->
	position_at_end (snd blocks.(i)) builder;
	let pow = power_i 2 (log_ty - i - 1) in
	let cst = const_shl (const_int mask_ty 1) (const_int mask_ty pow) in
	(*printf "case (1 << %d)\n" (power_i 2 (log_ty - i - 1));*)

	let n = build_load nptr "n" builder in
(*
	let _ = llvm_printf "log2: n(before) := " builder in
	let _ = build_call printi_ptr [| n |] "" builder in

	let _ = llvm_printf "log2: cst() := " builder in
	let _ = build_call printi_ptr [| cst |] "" builder in
*)
	let cmp = build_icmp Icmp.Ule cst n "cmp" builder in
	let _ = build_cond_br cmp (fst (blocks.(i))) (if i = log_ty -1 then exitb else snd (blocks.(i+1))) builder in
	position_at_end (fst blocks.(i)) builder;

	let res = build_load resptr "res" builder in
	let res = build_add res (const_int index_ty pow) "res" builder in
	let _ = build_store res resptr builder in
(*
	let _ = llvm_printf "log2: res(after) := " builder in
	let _ = build_call printi_ptr [| res |] "" builder in
*)
	let n = build_load nptr "n" builder in
	let n = build_lshr n (const_int index_ty pow) "n" builder in
	let _ = build_store n nptr builder in
(*
	let _ = llvm_printf "log2: n(after) := " builder in
	let _ = build_call printi_ptr [| n |] "" builder in
*)
	let _ = build_br (if i = log_ty -1 then exitb else snd (blocks.(i+1))) builder in
	()
      ) in
      position_at_end exitb builder;
      let res = build_load resptr "res" builder in
      let _ = build_ret res builder in
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(* 
   bitptrToIndex
*)
let bitptrToIndex () : llvalue =
  let fct_name = String.concat "_" ["bitptrToIndex"] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->
      let fct_ty = function_type index_ty [| pointer_type (struct_type context [| index_ty; mask_ty |]) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "bitptr" (params fct).(0) in
      let bitptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let indexptr = build_gep bitptr [| zero; zero |] "indexptr" builder in
      let index = build_load indexptr "index" builder in
(*
      let _ = llvm_printf "bitptrToIndex: index := " builder in
      let _ = build_call printi_ptr [| index |] "" builder in
*)
      let maskptr = build_gep bitptr [| zero; one |] "maskptr" builder in
      let mask = build_load maskptr "mask" builder in
(*
      let _ = llvm_printf "bitptrToIndex: mask := " builder in
      let _ = build_call printi_ptr [| mask |] "" builder in
*)    
      let index = build_mul index (const_int index_ty bitmap_unit_size) "index" builder in
(*
      let _ = llvm_printf "bitptrToIndex: base := " builder in
      let _ = build_call printi_ptr [| index |] "" builder in
*)
      let pow = build_call (log2 ()) [| mask |] "pow" builder in
(*
      let _ = llvm_printf "bitptrToIndex: pow := " builder in
      let _ = build_call printi_ptr [| pow |] "" builder in
*)
      let index = build_add index pow "index" builder in
(*
      let _ = llvm_printf "bitptrToIndex: res := " builder in
      let _ = build_call printi_ptr [| index |] "" builder in
*)
      let _ = build_ret index builder in
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(*
  isMarked
*)

let rec isMarked (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["isMarked"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type bool_type [| pointer_type (struct_type context [| index_ty; mask_ty |]); pointer_type (segment_type nbbulk bulksize) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "bitptr" (params fct).(0) in
      let bitptr = (params fct).(0) in

      let _ = set_value_name "segmentptr" (params fct).(1) in
      let segmentptr = (params fct).(1) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      (* we load the BM^j *)
      let bmptr = build_gep segmentptr [| zero; three; const_int (type_of zero) level |] "bmptr" builder in
      
      let indexptr = build_gep bitptr [| zero; zero |] "indexptr" builder in
      let index = build_load indexptr "index" builder in
(*
      let _ = llvm_printf "isMarked: index := " builder in
      let _ = build_call printi_ptr [| index |] "" builder in
*)
      let maskptr = build_gep bitptr [| zero; one |] "maskptr" builder in
      let mask = build_load maskptr "mask" builder in
(*
      let _ = llvm_printf "isMarked: mask := " builder in
      let _ = build_call printi_ptr [| mask |] "" builder in
*)
      let byteptr = build_gep bmptr [| const_int (type_of index) 0; index |] "byte" builder in
      let byte = build_load byteptr "byte" builder in
(*
      let _ = llvm_printf "isMarked: byte := " builder in
      let _ = build_call printi_ptr [| byte |] "" builder in
*)
      let byte = build_and mask byte "byte" builder in

      let cmp = build_icmp Icmp.Eq mask byte "cmp" builder in
      
      let _ = build_ret cmp builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);

      fct
;;

(*
  blockAddress
*)

let rec blockAddress (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["blockAddress"; string_of_int bulksize] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type (pointer_type (bulk_type bulksize)) [| pointer_type (struct_type context [| index_ty; mask_ty |]); pointer_type (segment_type nbbulk bulksize) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "bitptr" (params fct).(0) in
      let bitptr = (params fct).(0) in

      let _ = set_value_name "segmentptr" (params fct).(1) in
      let segmentptr = (params fct).(1) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let bulksptr = build_gep segmentptr [| zero; two |] "bulksptr" builder in

      let index = build_call (bitptrToIndex ()) [| bitptr |] "index" builder in
(*
      let _ = llvm_printf "blockAddress: index := " builder in
      let _ = build_call printi_ptr [| index |] "" builder in
*)
      let bulkptr = build_gep bulksptr [| const_int (type_of index) 0; index |] "bulkptr" builder in
      
      let _ = build_ret bulkptr builder in
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(* 
   incMaskBit
 *)
let rec incMaskBit (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["incMaskBit"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type bool_type [|pointer_type (struct_type context [| index_ty; mask_ty |]) |] in
      let fct = declare_function fct_name fct_ty modul in
      let _ = set_value_name "bitptr" (params fct).(0) in
      let bitptr = (params fct).(0) in
      let max_bitptr = max_bitptr bulksize level in
      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let block1 = append_block context "indexeq_testmask" fct in
      let block2 = append_block context "indexeq_maskeq" fct in

      let block3 = append_block context "indexneq_testmask" fct in
      let block4 = append_block context "indexneq_maskeq" fct in
      let block5 = append_block context "indexneq_maskneq" fct in

      (* we first test that the bitptr is not maximal *)
      let indexptr = build_gep bitptr [| zero; zero |] "indexptr" builder in
      let index = build_load indexptr "index" builder in

      let maskptr = build_gep bitptr [| zero; one |] "maskptr" builder in
      let mask = build_load maskptr "mask" builder in

      let max_indexptr = build_gep max_bitptr [| zero; zero |] "max_indexptr" builder in
      let max_index = build_load max_indexptr "max_index" builder in

      let cmp = build_icmp Icmp.Eq index max_index "cmp" builder in 
      let _ = build_cond_br cmp block1 block3 builder in

      position_at_end block1 builder;
      
      let max_maskptr = build_gep max_bitptr [| zero; one |] "max_maskptr" builder in
      let max_mask = build_load max_maskptr "max_mask" builder in

      let cmp = build_icmp Icmp.Eq mask max_mask "cmp" builder in 
      let _ = build_cond_br cmp block2 block3 builder in

      position_at_end block2 builder;

      let _ = build_ret false_ builder in

      position_at_end block3 builder;

      let cmp = build_icmp Icmp.Eq mask max_mask_value "cmp" builder in 
      let _ = build_cond_br cmp block4 block5 builder in
      
      position_at_end block4 builder;
      
      let _ = build_ret false_ builder in

      position_at_end block5 builder;

      let new_mask = build_shl mask (const_int (type_of index) 1) "shl" builder in
      let _ = build_store new_mask maskptr builder in
      let _ = build_ret true_ builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;


(*
  nextMask
*)

let rec nextMask (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["nextMask"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type bool_type [| pointer_type (struct_type context [| index_ty; mask_ty |]); pointer_type (segment_type nbbulk bulksize); bool_type |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "bitptr" (params fct).(0) in
      let bitptr = (params fct).(0) in

      let _ = set_value_name "segmentptr" (params fct).(1) in
      let segmentptr = (params fct).(1) in

      let _ = set_value_name "initinc" (params fct).(2) in
      let initinc = (params fct).(2) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let block1 = append_block context "loop" fct in

      let block2 = append_block context "failed" fct in

      let block3 = append_block context "test" fct in

      let block4 = append_block context "success" fct in      

      let _ = build_cond_br initinc block1 block3 builder in
      
      position_at_end block1 builder;
(*
      let _ = llvm_printf "nextMask: loop\n" builder in
*)
      let gonext = build_call (incMaskBit bulksize level) [| bitptr |] "gonext" builder in
      
      let _ = build_cond_br gonext block3 block2 builder in

      position_at_end block2 builder;
(*
      let _ = llvm_printf "nextMask: failed\n" builder in
*)    
      let _ = build_ret false_ builder in

      position_at_end block3 builder;
(*
      let _ = llvm_printf "nextMask: test\n" builder in
*)
      let ismarked = build_call (isMarked bulksize level) [| bitptr; segmentptr |] "ismarked" builder in

      let _ = build_cond_br ismarked block1 block4 builder in

      position_at_end block4 builder;
(*
      let _ = llvm_printf "nextMask: success\n" builder in
*)
      let _ = build_ret true_ builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec forwardBitPtr (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["forwardBitPtr"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type bool_type [| pointer_type (allocptr_type nbbulk bulksize) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "allocptr" (params fct).(0) in
      let allocptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      if level + 1 >= bitmap_depth nbbulk then (
	let _ = build_ret false_ builder in
	()
      )
      else
	(
	  let segmentptr = build_gep allocptr [| zero; zero |] "segmentptr" builder in
	  let segmentptr = build_load segmentptr "segmentptr" builder in
	  let bitptrj = build_gep allocptr [| zero; one; const_int (type_of zero) level |] "bitptrj" builder in
	  let bitptrjp1 = build_gep allocptr [| zero; one; const_int (type_of zero) (level + 1) |] "bitptrjp1" builder in

	  let idxj = build_gep bitptrj [| zero; zero |] "idxj" builder in
	  let idx = build_load idxj "idx" builder in
	  let _ = build_call (indexToBitPtr ()) [| bitptrjp1; idx |] "" builder in
	  
	  let maskjp1 = build_gep bitptrjp1 [| zero; one |] "maskjp1" builder in
	  let nm = build_call (nextMask bulksize (level + 1)) [| bitptrjp1; segmentptr; true_ |] "nm" builder in
	  
	  let block1 = append_block context "nm_fail" fct in
	  let block2 = append_block context "rec_fail" fct in
	  let block3 = append_block context "nm_or_rec_success" fct in

	  let _ = build_cond_br nm block3 block1 builder in

	  position_at_end block1 builder;
(*
	  let _ = llvm_printf "forwardBitPtr: nm_fail\n" builder in
*)	  
	  let rec_ = build_call (forwardBitPtr bulksize (level + 1)) [| allocptr |] "rec_" builder in
	  
	  let _ = build_cond_br rec_ block3 block2 builder in

	  position_at_end block2 builder;
(*
	  let _ = llvm_printf "forwardBitPtr: rec_fail\n" builder in
*)
	  let _ = build_ret false_ builder in
  
	  position_at_end block3 builder;
(*
	  let _ = llvm_printf "forwardBitPtr: nm_or_rec_success\n" builder in
*)
	  let idx = build_call (bitptrToIndex ()) [| bitptrjp1 |] "idx" builder in
	  let _ = build_store idx idxj builder in

	  let maskj = build_gep bitptrj [| zero; one |] "maskj" builder in	  
	  let _ = build_store (const_int mask_ty 1) maskj builder in

	  let _ = build_call (nextMask bulksize level) [| bitptrj; segmentptr; false_ |] "" builder in
	  
	  let _ = build_ret true_ builder in
	  ()
	);
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec findNextFreeBlock (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["findNextFreeBlock"; string_of_int bulksize ] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type bool_type [| pointer_type (allocptr_type nbbulk bulksize) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "allocptr" (params fct).(0) in
      let allocptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;
      
      let segmentptr = build_gep allocptr [| zero; zero |] "segmentptr" builder in
      let segmentptr = build_load segmentptr "segmentptr" builder in
      let bitptr0 = build_gep allocptr [| zero; one; const_int (type_of zero) 0 |] "bitptr0" builder in

      let found = build_call (nextMask bulksize 0) [| bitptr0; segmentptr; true_ |] "found" builder in
      
      let block1 = append_block context "nextMaskfailed" fct in

      let block2 = append_block context "forwardBitPtrfailed" fct in

      let block3 = append_block context "success" fct in

      let _ = build_cond_br found block3 block1 builder in

      position_at_end block1 builder;
(*
      let _ = llvm_printf "findNextFreeBlock: nextMaskfailed\n" builder in
*)
      let found = build_call (forwardBitPtr bulksize 0) [| allocptr |] "found" builder in
      
      let _ = build_cond_br found block3 block2 builder in

      position_at_end block2 builder;
(*
      let _ = llvm_printf "findNextFreeBlock: forwardBitPtrfailed\n" builder in
*)
      let _ = build_ret false_ builder in

      position_at_end block3 builder;
(*
      let _ = llvm_printf "findNextFreeBlock: success\n" builder in
*)
      let bulkptr = build_call (blockAddress bulksize) [| bitptr0; segmentptr |] "bulkptr" builder in

      let bulkptrptr = build_gep allocptr [| zero; two |] "bulkptrptr" builder in
      let _ = build_store bulkptr bulkptrptr builder in

      let _ = build_ret true_ builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec setBit (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["setBit"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type void_type [| pointer_type (allocptr_type nbbulk bulksize) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "allocptr" (params fct).(0) in
      let allocptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let segmentptr = build_gep allocptr [| zero; zero |] "segmentptr" builder in
      let segmentptr = build_load segmentptr "segmentptr" builder in

      let bitjptr = build_gep allocptr [| zero; one; const_int (type_of zero) level |] "bitptrj" builder in

      let bmjptr = build_gep segmentptr [| zero; three; const_int (type_of zero) level |] "bmjptr" builder in
      
      let idxjptr = build_gep bitjptr [| zero; zero |] "idxjptr" builder in
      let idxj = build_load idxjptr "idxj" builder in

      let maskjptr = build_gep bitjptr [| zero; one |] "maskjptr" builder in
      let maskj = build_load maskjptr "maskj" builder in

      let bmjidxjptr = build_gep bmjptr [| const_int (type_of idxj) 0; idxj |] "bmjidxjptr" builder in
      let bmjidxj = build_load bmjidxjptr "bmjidxj" builder in

      let newbmjidxj = build_or bmjidxj maskj "newbmjidxj" builder in

      let _ = build_store newbmjidxj bmjidxjptr builder in 

      if level + 1 >= bitmap_depth nbbulk then 
	let _ = build_ret_void builder in () 
      else (

	let full = const_all_ones (type_of newbmjidxj) in
	let cmp = build_icmp Icmp.Eq full newbmjidxj "cmp" builder in

	let block1 = append_block context "isfull" fct in
	let block2 = append_block context "isnotfull" fct in

	let _ = build_cond_br cmp block1 block2 builder in
	
	position_at_end block2 builder;
	let _ = build_ret_void builder in

	position_at_end block1 builder;

	let bitptrjp1ptr = build_gep allocptr [| zero; one; const_int (type_of zero) (level + 1) |] "bitptrjp1ptr" builder in
	
	let _ = build_call (indexToBitPtr ()) [| bitptrjp1ptr; idxj |] "" builder in
	
	let _ = build_call (setBit bulksize (level + 1)) [| allocptr |] "" builder in

	let _ = build_ret_void builder in
	()
      );

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(* 
   incBulkPtr
 *)
let rec incBulkPtr (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["incBulkPtr"; string_of_int bulksize] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type void_type [| pointer_type (bulkptr_type bulksize) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "bulkptr" (params fct).(0) in
      let bulkptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let oldbulkptr = build_load bulkptr "oldbulkptr" builder in

      let newbulkptr = build_gep oldbulkptr [| one |] "newbulkptr" builder in

      let _ = build_store newbulkptr bulkptr builder in

      let _ = build_ret_void builder in
      
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(* 
   inc
 *)
let rec inc (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["inc"; string_of_int bulksize] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type void_type [| pointer_type (allocptr_type nbbulk bulksize) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "allocptr" (params fct).(0) in
      let allocptrptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let bulkptrptr = build_gep allocptrptr [| zero; two |] "bulkptrptr" builder in
      let _ = build_call (incBulkPtr bulksize) [| bulkptrptr |] "" builder in

      let bitptr = build_gep allocptrptr [| zero; one; zero |] "bitptr" builder in
      let _ = build_call (incBitPtr bulksize 0) [| bitptr |] "" builder in       

      let _ = build_ret_void builder in
      
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec tryAlloc (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["tryAlloc"; string_of_int bulksize] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type (pointer_type (bulk_type bulksize)) [| pointer_type (allocptr_type nbbulk bulksize) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "allocptr" (params fct).(0) in
      let allocptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let segmentptr = build_gep allocptr [| zero; zero |] "segmentptr" builder in
      let segmentptr = build_load segmentptr "segmentptr" builder in

      let bitptr0 = build_gep allocptr [| zero; one; const_int (type_of zero) 0 |] "bitptr0" builder in

      let ismarked = build_call (isMarked bulksize 0) [| bitptr0; segmentptr |] "ismarked" builder in

      let found = append_block context "found" fct in
      let is_marked = append_block context "is_marked" fct in
      let not_found = append_block context "not_found" fct in

      let _ = build_cond_br ismarked is_marked found builder in

      position_at_end is_marked builder;
(*
      let _ = llvm_printf "tryAlloc: is_marked\n" builder in
*)
      let is_founded = build_call (findNextFreeBlock bulksize) [| allocptr |] "is_founded" builder in
      
      let _ = build_cond_br is_founded found not_found builder in
      
      position_at_end not_found builder;
(*
      let _ = llvm_printf "tryAlloc: not_found\n" builder in
*)
      let _ = build_ret (const_null (pointer_type (bulk_type bulksize))) builder in

      position_at_end found builder;
(*
      let _ = llvm_printf "tryAlloc: found\n" builder in
*)
      let bulkptrptr = build_gep allocptr [| zero; two |] "bulkptrptr" builder in
      let bulkptr = build_load bulkptrptr "bulkptr" builder in

      let _ = build_call (setBit bulksize 0) [| allocptr |] "" builder in

      let _ = build_call (inc bulksize) [| allocptr |] "" builder in

      let _ = build_ret bulkptr builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec mark_and_push (bulksize: int) : llvalue = 
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["mark_and_push"; string_of_int bulksize] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type void_type [| ptri8_type |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "o" (params fct).(0) in
      let o = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let _ = llvm_printf (String.concat "" [fct_name; ": "]) builder in
      let _ = build_call printp_ptr [| o |] "" builder in
      
      let _ = build_ret_void builder in
  
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec clear (bulksize: int) : llvalue = 
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["clear"; string_of_int bulksize] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type void_type [| ptri8_type |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "ptr" (params fct).(0) in
      let ptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let _ = llvm_printf (String.concat "" [fct_name; ": "]) builder in
      let _ = build_call printp_ptr [| ptr |] "" builder in

      let segmentptr = build_bitcast ptr (pointer_type (segment_type nbbulk bulksize)) "segmentptr" builder in

      (* count to zero *)
      let counterptr = build_gep segmentptr [| zero; one |] "counterptr" builder in
      let _ = build_store (const_null (segment_count_type nbbulk)) counterptr builder in

      (* all bitmap to zero *)
      let bitmapptr = build_gep segmentptr [| zero; three |] "bitmapptr" builder in
      let bitmapptr = build_bitcast bitmapptr ptri8_type "bitmapptr" builder in
      (* bitmap_type nbbulk *)
      let _ = build_call memset_ptr [| bitmapptr; const_int size_type 0; const_int size_type (bitmap_size nbbulk) |] "" builder in
      

      let _ = build_ret_void builder in
  
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec create_Segment (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["create_Segment"; string_of_int bulksize] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type (pointer_type (segment_type nbbulk bulksize)) [| |] in
      let fct = declare_function fct_name fct_ty modul in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let ptr = build_call memalign_ptr [| const_int size_type max_segment_size; const_int size_type max_segment_size |] "ptr" builder in

      let _ = build_call memset_ptr [| ptr; const_int size_type 0; const_int size_type max_segment_size |] "" builder in

      let segmentptr = build_bitcast ptr (pointer_type (segment_type nbbulk bulksize)) "segmentptr" builder in

      let fctptr = build_gep segmentptr [| zero; zero; zero |] "fctptr" builder in
      let _ = build_store (mark_and_push bulksize) fctptr builder in

      let fctptr = build_gep segmentptr [| zero; zero; one |] "fctptr" builder in
      let _ = build_store (clear bulksize) fctptr builder in

      let _ = build_call printp_ptr [| ptr |] "" builder in
      
      let _ = build_ret segmentptr builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec create_allocptr (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["create_allocptr"; string_of_int bulksize] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type void_type [| pointer_type (segment_type nbbulk bulksize); pointer_type (allocptr_type nbbulk bulksize) |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "segmentptr" (params fct).(0) in
      let segmentptr = (params fct).(0) in

      let _ = set_value_name "allocptr" (params fct).(1) in
      let allocptr = (params fct).(1) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let segmentptrptr = build_gep allocptr [| zero; zero |] "segmentptrptr" builder in
      let _ = build_store segmentptr segmentptrptr builder in

      let bitptr0 = build_gep allocptr [| zero; one; const_int (type_of zero) 0 |] "bitptr0" builder in
      let bulkptr = build_gep allocptr [| zero; two |] "bulkptr" builder in
      
      let idx0 = build_gep bitptr0 [| zero; zero |] "idx0" builder in
      let mask0 = build_gep bitptr0 [| zero; one |] "mask0" builder in

      let _ = build_store (const_null index_ty) idx0 builder in
      let _ = build_store (const_int mask_ty 1) mask0 builder in

      let bulkptrptr = build_gep segmentptr [| zero; two; zero |] "bulkptrptr" builder in
      let _ = build_store bulkptrptr bulkptr builder in

      let _ = build_ret_void builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec mark_and_push () : llvalue =
  let fct_name = String.concat "_" ["mark_and_push"] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type void_type [| ptri8_type |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "o" (params fct).(0) in
      let o = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let max_ptri8 = const_all_ones size_type in
      let segmask = const_not (const_int size_type (power_i 2 max_segment_size_bit - 1)) in
      let segmask = const_and max_ptri8 segmask in

      let o' = build_ptrtoint o size_type "o" builder in

      let segptr = build_and o' segmask "segptr" builder in

      let segptr = build_inttoptr segptr ptri8_type "segptr" builder in
      
      let _ = llvm_printf "segment* := " builder in
      let _ = build_call printp_ptr [| segptr |] "" builder in

      let segment_ptr = build_bitcast segptr (pointer_type segment_fct_ptr) "segment_ptr" builder in
      let mapptrptr = build_gep segment_ptr [| zero; zero |] "mapptrptr" builder in
      let mapptr = build_load mapptrptr "mapptr" builder in
      let _ = build_call mapptr [| o |] "" builder in
      let _ = build_ret_void builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let rec clear () : llvalue =
  let fct_name = String.concat "_" ["clear"] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type void_type [| ptri8_type |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "ptr" (params fct).(0) in
      let ptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let segment_ptr = build_bitcast ptr (pointer_type segment_fct_ptr) "segment_ptr" builder in
      let clearptrptr = build_gep segment_ptr [| zero; one |] "clearptrptr" builder in
      let clearptr = build_load clearptrptr "clearptr" builder in
      let _ = build_call clearptr [| ptr |] "" builder in

      let _ = build_ret_void builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;


(*
(* code gen of every functions *)
let _ = 
  Array.init (value_ty_size + 2 - 1) (fun i ->
    let bulksize = i + 2 in
    let nbbulk = nbbulk_from_bulksize bulksize in
    printf "bulksize := %d --> nbbulk := %d, ty := %s\n" bulksize nbbulk (string_of_lltype (segment_type nbbulk bulksize)); flush stdout;
    let _ = Array.init (bitmap_depth nbbulk) (fun i ->
      printf "\tlevel := %d, max mask := %d\n" i (bimap_level_last_mask nbbulk i); flush stdout;
      let _ = incBitPtr bulksize i in
      let _ = isMarked bulksize i in
      let _ = nextMask bulksize i in
      let _ = forwardBitPtr bulksize i in
      let _ = setBit bulksize i in 
      ()
    ) in
    let _ = findNextFreeBlock bulksize in
    let _ = blockAddress bulksize in
    let _ = incBulkPtr bulksize in
    let _ = inc bulksize in
    let _ = tryAlloc bulksize in
    ()
  );
  let _ = indexToBitPtr () in
  let _ = bitptrToIndex () in
  (*let _ = dump_module modul in*)
  ()
;;
*)
(* a test *)

let testfct = 
  let fct_name = String.concat "_" ["testAlloc"] in
  let fct_ty = function_type void_type [| |] in
  let fct = declare_function fct_name fct_ty modul in
  let entryb = append_block context "entry" fct in
  let builder = builder context in
  position_at_end entryb builder;
  
  let bulksize = 20 in
  let nbbulk = nbbulk_from_bulksize bulksize in

  printf "bulksize := %d --> nbbulk := %d, ty := %s\n" bulksize nbbulk (string_of_lltype (segment_type nbbulk bulksize)); flush stdout;
  
    (* create a segment and its allocation pointer *)
  let segmentptr = build_call (create_Segment bulksize) [| |] "segmentptr" builder in
  let allocptr = build_alloca (allocptr_type nbbulk bulksize) "allocptr" builder in
  let _ = build_call (create_allocptr bulksize) [| segmentptr; allocptr |] "" builder in
  
    (* do some allocation and print it *)
  let _ = Array.init (nbbulk + 1) (fun i ->

    let bulkptr = build_call (tryAlloc bulksize) [| allocptr |] "bulkptr" builder in
    let ptr = build_bitcast bulkptr (ptri8_type) "ptr" builder in
    let _ = llvm_printf "allocated bulk* := " builder in
    let _ = build_call printp_ptr [| ptr |] "" builder in
    if i = nbbulk then () else (
      let _ = build_call (mark_and_push ()) [| ptr |] "" builder in
      ()
    );
    
    let _ = llvm_printf "\n" builder in
    ()
  ) in

  let segmentptr' = build_bitcast segmentptr ptri8_type "segmentptr'" builder in
  let _ = build_call (clear ()) [| segmentptr' |] "" builder in
  let _ = build_call (create_allocptr bulksize) [| segmentptr; allocptr |] "" builder in

  let bulkptr = build_call (tryAlloc bulksize) [| allocptr |] "bulkptr" builder in
  let ptr = build_bitcast bulkptr (ptri8_type) "ptr" builder in
  let _ = llvm_printf "allocated bulk* := " builder in
  let _ = build_call printp_ptr [| ptr |] "" builder in
  let _ = build_ret_void builder in
  
  Llvm_analysis.assert_valid_function fct;
  if !optimize then ignore(PassManager.run_function fct pass_manager);
  fct
;;

let _ = ExecutionEngine.run_function testfct [| |] engine;;

(*let _ = dump_module modul;;*)

(******************* mymms Compiler **********************)

