open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;

open Printf;;

open State;;

(* some parameters *)

(* value_type: used as bulk unit *)

let value_size_bits : int = Int64.to_int (size_in_bits target_data ptri8_type);;
let value_type : lltype = integer_type context value_size_bits;;
let value_size_bytes : int = Int64.to_int (abi_size target_data value_type);;
let value_align : int = abi_align target_data value_type;;

(* bitmap_type: used as bitmap unit*)

let bitmap_size_bits : int = Int64.to_int (size_in_bits target_data ptri8_type);;
let bitmap_type : lltype = integer_type context bitmap_size_bits;;
let bitmap_size_bytes : int = Int64.to_int (abi_size target_data bitmap_type);;
let bitmap_align : int = abi_align target_data bitmap_type;;


(* we can compute the number of less-significant bits irrelevant in a ptr *)
let free_bits : int = int_of_float ((log (float (abi_align target_data ptri8_type))) /. log 2.);;

printf "free_bits := %d\n" free_bits;;

flush stdout;;

(* make sure we have at least 2 bits *)
assert (free_bits >= 2);;

(* alignment of segments as a power of 2 *)
let segment_alignment_log : int = 12;;
let segment_max_size_bytes : int = power_i 2 segment_alignment_log
;;

(* segment type *)
(* nbbulk: number of bulk *)
(* bulksize: size of a bulk *)

(* the type of the counter of allocated bulk in the segment *)
let segment_count_type (nbbulk: int) : lltype = integer_type context (log_i nbbulk 2);;

(* the type of a bulk *)
let bulk_type (bulksize: int) : lltype = array_type value_type bulksize;;

(* the type of the array of bulk *)
let segment_bulk_type (nbbulk: int) (bulksize: int) : lltype = array_type (bulk_type bulksize) nbbulk;;

(* the depth of the bitmap *)
let bitmap_depth (nbbulk: int) : int = log_i nbbulk bitmap_size_bits;;

(* the number of bitmap per level *)
let bitmap_per_level (nbbulk: int) (level: int) : int = 
  let nb_level = bitmap_depth nbbulk in
  if level >= nb_level then raise (Failure "level overflow");
  if level < 0 then raise (Failure "level overflow");
  let n = ref level in
  let res = ref (div_i nbbulk bitmap_size_bits) in
  while !n != 0 do
    res := div_i !res bitmap_size_bits;
    n := !n - 1;      
  done;
  !res
;;

(* the last valid bit *)
let bimap_last_bit (nbbulk: int) (level: int) : int =
  let nb_level = bitmap_depth nbbulk in
  if level >= nb_level then raise (Failure "level overflow");
  if level < 0 then raise (Failure "level overflow");
  let nbelt = if level = 0 then nbbulk else bitmap_per_level nbbulk (level - 1) in
  let divs = div_i nbelt bitmap_size_bits in
  let rest = divs * bitmap_size_bits - nbelt in
  bitmap_size_bits - rest - 1
;;

(* the type of the bitmap *)
let bitmap_levels_size (nbbulk: int) : int array =
  let nb_level = bitmap_depth nbbulk in
  Array.init nb_level (fun i ->
    let sz = bitmap_per_level nbbulk i in
    (*printf "|BM^%d| := %d\n" i sz; flush stdout;*)
    sz
  )
;;

let segment_bitmap_type (nbbulk: int) : lltype =
  let a = bitmap_levels_size nbbulk in
  let a = Array.map (fun i -> array_type bitmap_type i) a in
  struct_type context a
;;

let bitmap_size (nbbulk: int) : int =
  Int64.to_int (abi_size target_data (segment_bitmap_type nbbulk));;

(* the header of a segment: some sizeless representation which allow manipulation of any segment *)
(* the header of a heap: some sizeless representation which allow manipulation of any heap *)
let headers : lltype * lltype = 
  let seghd_ty = opaque_type context in
  let heaphd_ty = opaque_type context in
  let seghd_handle = handle_to_type seghd_ty in
  let heaphd_handle = handle_to_type heaphd_ty in

  let seghd_recdef = 
    struct_type context [|
      pointer_type seghd_ty; (* prev *)
      pointer_type seghd_ty; (* next *)
      pointer_type heaphd_ty; (* heap header *)
			|] in
  let heaphd_recdef = 
    struct_type context [| 
      pointer_type (function_type void_type [| value_type; pointer_type seghd_ty |]); (* mark_and_push *) 
      pointer_type (function_type void_type [| pointer_type seghd_ty |]); (* clear *)
      pointer_type (function_type void_type [| value_type; pointer_type seghd_ty |]) (* free *)
			|] in

  let _ = refine_type seghd_ty seghd_recdef in
  let _ = refine_type heaphd_ty heaphd_recdef in
  let seghd_ty = type_of_handle seghd_handle in
  let heaphd_ty = type_of_handle heaphd_handle in
  let _ = define_type_name "segment_header" seghd_ty modul in
  let _ = define_type_name "heap_header" heaphd_ty modul in
  (seghd_ty, heaphd_ty)
;;

let segment_header_type : lltype = fst headers;;
let heap_header_type : lltype = snd headers;;

(* a segment type *)
let segment_type (nbbulk: int) (bulksize: int) : lltype =
  let ty = struct_type context [| 
    segment_header_type;
    segment_count_type nbbulk; 
    segment_bulk_type nbbulk bulksize; 
    segment_bitmap_type nbbulk
			       |] in
  (*printf "segment_type := %s\n" (string_of_lltype ty); flush stdout;*)
  ty
;;

(* the size in bytes of a segments *)
let segment_size_bytes (nbbulk: int) (value_per_bulk: int) : int =
    let segment_ex_type = segment_type nbbulk value_per_bulk in
    Int64.to_int (abi_size target_data segment_ex_type)
;;

(* given the max_segment_size, compute the number of bulk given their size *)
let nbbulk_from_bulksize (bulksize: int) : int =
  let sz = ref 0 in
  let loop = ref true in
  while !loop do
    if segment_size_bytes (!sz + 1) bulksize > segment_max_size_bytes then loop := false else sz := !sz + 1
  done;
  !sz
;;

(* gives the maximum bulksize such that a segment can at least hold one bulk *)
let max_bulksize: int =
  let max = ref 1 in
  while nbbulk_from_bulksize !max > 0 do
    max := !max + 1
  done;
  !max
;;

let _ = printf "max_bulksize := %d ( # %d k.o.)\n" max_bulksize (max_bulksize * value_size_bytes / 1024);;

(* a bitptr is a pair of an index and a mask *)
let index_type : lltype = bitmap_type;;
let mask_type : lltype = bitmap_type;;
let bitptr_type : lltype = struct_type context [| index_type; mask_type |]

let bitptr_index_mask (bitptr: llvalue) (builder: llbuilder) : (llvalue * llvalue) * (llvalue * llvalue) =
  
  let indexptr = build_gep bitptr [| zero; zero |] "indexptr" builder in
  let index = build_load indexptr "index" builder in
  
  let maskptr = build_gep bitptr [| zero; one |] "maskptr" builder in
  let mask = build_load maskptr "mask" builder in

  ((indexptr, index), (maskptr, mask))

let max_mask_value : llvalue = const_shl (const_int bitmap_type 1) (const_int bitmap_type (bitmap_size_bits - 1));;
let min_mask_value : llvalue = const_int bitmap_type 1;;

let bitptrs_type (nbbulk: int) : lltype = 
  array_type bitptr_type (bitmap_depth nbbulk);;

(* the type of a bulk pointer *)
let bulkptr_type (bulksize: int) : lltype = pointer_type (bulk_type bulksize);; 

(* the type of an allocation pointer *)
let allocptr_type (nbbulk: int) (bulksize: int) : lltype = struct_type context [| 
  pointer_type (segment_type nbbulk bulksize); 
  bitptrs_type nbbulk; 
  bulkptr_type bulksize 
									       |];;

(* the heap *)
let hi (bulksize: int) : lltype = 
  let nbbulk = nbbulk_from_bulksize bulksize in
  struct_type context [|
    heap_header_type;
    pointer_type segment_header_type; (* pointer to the first segment *)
    pointer_type segment_header_type; (* pointer to the last segment *)
    allocptr_type nbbulk bulksize;
		      |]
;;

let heap_type (bulksizes: int array) : lltype =
  struct_type context [|
    pointer_type segment_header_type; (* the list of free segment *)
    struct_type context (Array.map (fun bulksize ->
      hi bulksize
    ) bulksizes
    ) (* the list of different allocator *)
		      |];;

(* we create the heap *)
let heap, heap_ty = 
  let bulksizes = Array.init (*max_bulksize*) 2 (fun i -> i + 1) in
  let heap_ty = heap_type bulksizes in
  let init_heap = const_null heap_ty in
  let init_heap_size = Int64.to_int (abi_size target_data heap_ty) in
  let heap_name = "heap" in
  printf "|heap| := %d o\n" init_heap_size;
  printf "|heap| := %d ko\n" (init_heap_size / 1024);
  let _ = define_type_name "heap" heap_ty modul in
  define_global heap_name init_heap modul, pointer_type heap_ty
;;


(* we are going to build dynamically static functions in llvm *)

(* the global maxbitptr *)

let max_bitptr (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let var_name = String.concat "_" ["max_bitptr"; string_of_int bulksize; string_of_int level] in
  match lookup_global var_name modul with
    | Some v -> v
    | None ->
      let max_index = bitmap_per_level nbbulk level - 1 in
      let max_mask = power_i 2 (bimap_last_bit nbbulk level) in
      let init = const_struct context [| const_int index_type max_index; const_int mask_type max_mask |] in
      define_global var_name init modul
;;

(* 
   incBitPtr
*)
let rec incBitPtr (bulksize: int) (level: int) : llvalue =
  let fct_name = String.concat "_" ["incBitPtr"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->
      let fct_ty = function_type bool_type [| pointer_type bitptr_type |] in
      let fct = declare_function fct_name fct_ty modul in
      let _ = set_value_name "bitptr" (params fct).(0) in
      let bitptr = (params fct).(0) in

      (* we grab the maximal bitptr value for this size and level *)
      let max_bitptr = max_bitptr bulksize level in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let block1 = append_block context "indexeq_testmask" fct in
      let block2 = append_block context "indexeq_maskeq" fct in

      let block3 = append_block context "indexneq_testmask" fct in
      let block4 = append_block context "indexneq_maskeq" fct in
      let block5 = append_block context "indexneq_maskneq" fct in

      (* we first test that the bitptr index is not maximal *)
      let indexptr = build_gep bitptr [| zero; zero |] "indexptr" builder in
      let index = build_load indexptr "index" builder in

      let maskptr = build_gep bitptr [| zero; one |] "maskptr" builder in
      let mask = build_load maskptr "mask" builder in

      let max_indexptr = build_gep max_bitptr [| zero; zero |] "max_indexptr" builder in
      let max_index = build_load max_indexptr "max_index" builder in

      let cmp = build_icmp Icmp.Eq index max_index "cmp" builder in 
      let _ = build_cond_br cmp block1 block3 builder in

      position_at_end block1 builder;
      
      (* the index is maximal, is the mask maximal? *)
      let max_maskptr = build_gep max_bitptr [| zero; one |] "max_maskptr" builder in
      let max_mask = build_load max_maskptr "max_mask" builder in

      let cmp = build_icmp Icmp.Eq mask max_mask "cmp" builder in 
      let _ = build_cond_br cmp block2 block3 builder in

      position_at_end block2 builder;

      (* we are on the maximum index/mask, we cannot increment the bitptr *)
      let _ = build_ret false_ builder in

      position_at_end block3 builder;

      (* the index is not maximal, is the mask maximal? *)

      let cmp = build_icmp Icmp.Eq mask max_mask_value "cmp" builder in 
      let _ = build_cond_br cmp block4 block5 builder in
      
      position_at_end block4 builder;
      
      (* the mask is maximal, thus we increment the index, and reset the mask *)

      let new_index = build_add index (const_int (type_of index) 1) "add" builder in
      let _ = build_store new_index indexptr builder in
      let _ = build_store min_mask_value maskptr builder in
      let _ = build_ret true_ builder in

      position_at_end block5 builder;

      (* the mask is not maximal, we increment it *)

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
      let fct_ty = function_type void_type [| pointer_type bitptr_type; index_type |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "bitptr" (params fct).(0) in
      let bitptr = (params fct).(0) in

      let _ = set_value_name "index" (params fct).(1) in
      let index = (params fct).(1) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      (* the bitptr index is the index divided by the bitmap unit size 
	 the mask is a shift by the rest of the previous division
      *)

      let idx = build_udiv index (const_int (type_of index) bitmap_size_bits) "idx" builder in
      let rem = build_urem index (const_int (type_of index) bitmap_size_bits) "rem" builder in
      let mask = build_shl (const_int mask_type 1) rem "mask" builder in

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
  helper used for the next function 
*)

let log2 () : llvalue =
  let fct_name = String.concat "_" ["log2"] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->
      let fct_ty = function_type index_type [| mask_type |] in
      let fct = declare_function fct_name fct_ty modul in
      let _ = set_value_name "n" (params fct).(0) in
      let n = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let exitb = append_block context "exit" fct in
      let builder = builder context in
      position_at_end entryb builder;

      let resptr = build_alloca index_type "resptr" builder in
      let _ = build_store (const_int index_type 0) resptr builder in

      let nptr = build_alloca index_type "nptr" builder in
      let _ = build_store n nptr builder in

      let sz = Int64.to_int (size_in_bits target_data mask_type) in
      let log_ty = log_i sz 2 in
      assert (power_i 2 log_ty = sz);
      let blocks = Array.init log_ty (fun i ->
	append_block context "casetrue" fct, append_block context "next" fct
      ) in
      let _ = build_br (snd blocks.(0)) builder in      
      let _ = Array.init log_ty (fun i ->
	position_at_end (snd blocks.(i)) builder;
	let pow = power_i 2 (log_ty - i - 1) in
	let cst = const_shl (const_int mask_type 1) (const_int mask_type pow) in
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
	let res = build_add res (const_int index_type pow) "res" builder in
	let _ = build_store res resptr builder in
(*
	let _ = llvm_printf "log2: res(after) := " builder in
	let _ = build_call printi_ptr [| res |] "" builder in
*)
	let n = build_load nptr "n" builder in
	let n = build_lshr n (const_int index_type pow) "n" builder in
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
      let fct_ty = function_type index_type [| pointer_type bitptr_type |] in
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
      (* the index base is the bitptr index multiply by the bitmap unit size ... *)
      let index = build_mul index (const_int index_type bitmap_size_bits) "index" builder in
(*
      let _ = llvm_printf "bitptrToIndex: base := " builder in
      let _ = build_call printi_ptr [| index |] "" builder in
*)
      (* ... plus the log2 of the mask *)

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

  given a bitptr and a semgment, check if the corresponding bitmap of a given level is set 
*)

let rec isMarked (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["isMarked"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type bool_type [| pointer_type bitptr_type; pointer_type (segment_type nbbulk bulksize) |] in
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

      (* we grab the bitmap *)
      let byteptr = build_gep bmptr [| const_int (type_of index) 0; index |] "byte" builder in
      let byte = build_load byteptr "byte" builder in
(*
      let _ = llvm_printf "isMarked: byte := " builder in
      let _ = build_call printi_ptr [| byte |] "" builder in
*)

      (* we do a and with the mask and check if it is equal to the mask *)
      let byte = build_and mask byte "byte" builder in

      let cmp = build_icmp Icmp.Eq mask byte "cmp" builder in
      
      let _ = build_ret cmp builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);

      fct
;;

(*
  blockAddress

  given a bitptr (of level 0) and a segment, return the corresponding bulk ptr
*)

let rec blockAddress (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["blockAddress"; string_of_int bulksize] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type (pointer_type (bulk_type bulksize)) [| pointer_type bitptr_type; pointer_type (segment_type nbbulk bulksize) |] in
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
  let fct_name = String.concat "_" ["incMaskBit"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type bool_type [|pointer_type bitptr_type |] in
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

  for a given bitptr of a given level, try to increment the mask until a unset bit is found (return true if found, false otherwise
*)

let rec nextMask (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["nextMask"; string_of_int bulksize; string_of_int level] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type bool_type [| pointer_type bitptr_type; pointer_type (segment_type nbbulk bulksize); bool_type |] in
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

(*
  forwardBitPtr

  try to find an unset bit of an allocptr (given levels of bitptr + segment pointer)
*)

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
	  
	  (*let maskjp1 = build_gep bitptrjp1 [| zero; one |] "maskjp1" builder in*)
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
	  let _ = build_store (const_int mask_type 1) maskj builder in

	  let _ = build_call (nextMask bulksize level) [| bitptrj; segmentptr; false_ |] "" builder in
	  
	  let _ = build_ret true_ builder in
	  ()
	);
      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(* 

   findNextFreeBlock

   set the bulkptr / bitptrs of an allocator pointer to the next free block (true if found, false otherwise)
*)

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

(* 

   setBit

   set a bitmap bit given its bitptr (keep higher level consistant with the new marking)

*)

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

   unsetBit

   unset a bitmap bit given its bitptr (keep higher level consistant with the new marking)

*)

let rec unsetBit (bulksize: int) (level: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["unsetBit"; string_of_int bulksize; string_of_int level] in
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
      let bmjidxj = build_not bmjidxj "bmjidxj" builder in

      let newbmjidxj = build_and bmjidxj maskj "newbmjidxj" builder in

      let _ = build_store newbmjidxj bmjidxjptr builder in 

      if level + 1 >= bitmap_depth nbbulk then 
	let _ = build_ret_void builder in () 
      else (

	let empty = const_null (type_of newbmjidxj) in
	let cmp = build_icmp Icmp.Eq empty newbmjidxj "cmp" builder in

	let block1 = append_block context "isempty" fct in
	let block2 = append_block context "isnotempty" fct in

	let _ = build_cond_br cmp block1 block2 builder in
	
	position_at_end block2 builder;
	let _ = build_ret_void builder in

	position_at_end block1 builder;

	let bitptrjp1ptr = build_gep allocptr [| zero; one; const_int (type_of zero) (level + 1) |] "bitptrjp1ptr" builder in
	
	let _ = build_call (indexToBitPtr ()) [| bitptrjp1ptr; idxj |] "" builder in
	
	let _ = build_call (unsetBit bulksize (level + 1)) [| allocptr |] "" builder in

	let _ = build_ret_void builder in
	()
      );

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(* 
   incBulkPtr

   increment the bulkptr 
 *)
let rec incBulkPtr (bulksize: int) : llvalue =
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
   
   increment both bulkptr and bitptr of an allocator pointer
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

(*
  init_allocptr
*)

let rec init_allocptr (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["init_allocptr"; string_of_int bulksize] in
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

      let _ = build_store (const_null index_type) idx0 builder in
      let _ = build_store (const_int mask_type 1) mask0 builder in

      let bulkptrptr = build_gep segmentptr [| zero; two; zero |] "bulkptrptr" builder in
      let _ = build_store bulkptrptr bulkptr builder in

      let _ = build_ret_void builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct

;;

(*
  nextSegment

  try to shift the allocation pointer to the next segment
*)
let rec nextSegment (bulksize: int) : llvalue =
  let nbbulk = nbbulk_from_bulksize bulksize in
  let fct_name = String.concat "_" ["nextSegment"; string_of_int bulksize] in
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

      let nextsegmentptr = build_gep segmentptr [| zero; zero; one |] "nextsegmentptr" builder in
      let nextsegmentptr = build_bitcast nextsegmentptr (pointer_type (segment_type nbbulk bulksize)) "nextsegmentptr" builder in

      (* we test if the next segment is null *)
      let isnull = build_is_null nextsegmentptr "isnull" builder in

      let block1 = append_block context "next is null" fct in
      let block2 = append_block context "next is not null" fct in

      let _ = build_cond_br isnull block1 block2 builder in

      position_at_end block1 builder;

      let _ = build_ret false_ builder in

      position_at_end block2 builder;

      (* initialize the allocation pointer *)
      let _ = build_call (init_allocptr bulksize) [| nextsegmentptr; allocptr |] "" builder in
      
      let _ = build_ret true_ builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;      


(*
  tryAlloc

  try allocating a fresh bulk given an allocation pointer (try allocating into a segment)
*)

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

      (* we try to go to the next segment *)
      let gonext = build_call (nextSegment nbbulk) [| allocptr |] "gonext" builder in

      let can_gonext = append_block context "can gonext" fct in
      let cannot_gonext = append_block context "cannot gonext" fct in

      let _ = build_cond_br gonext can_gonext cannot_gonext builder in

      position_at_end cannot_gonext builder;

      (* there is no such next segment, we failed *)
      let _ = build_ret (const_null (pointer_type (bulk_type bulksize))) builder in

      position_at_end can_gonext builder;

      (* there is a next segment, we recursively call the allocation routine *)
      let res = build_call (tryAlloc bulksize) [| allocptr |] "res" builder in

      let _ = build_ret res builder in

      position_at_end found builder;
(*
      let _ = llvm_printf "tryAlloc: found\n" builder in
*)
      let bulkptrptr = build_gep allocptr [| zero; two |] "bulkptrptr" builder in
      let bulkptr = build_load bulkptrptr "bulkptr" builder in

      let _ = build_call (setBit bulksize 0) [| allocptr |] "" builder in

      let _ = build_call (inc bulksize) [| allocptr |] "" builder in

      let counterptr = build_gep segmentptr [| zero; one |] "counterptr" builder in
      let counter = build_load counterptr "counter" builder in
      let newcounter = build_add counter (const_int (type_of counter) 1) "newcounter" builder in
      let _ = build_store newcounter counterptr builder in

      let _ = build_ret bulkptr builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

(*
  create a new segment, and store it into a heap free segment list
*)
let rec create_Segment () : llvalue =
  let fct_name = String.concat "_" ["create_Segment"] in
  match lookup_function fct_name modul with
    | Some fct -> fct
    | None ->

      let fct_ty = function_type void_type [| heap_ty |] in
      let fct = declare_function fct_name fct_ty modul in

      let _ = set_value_name "heap_ptr" (params fct).(0) in
      let heap_ptr = (params fct).(0) in

      let entryb = append_block context "entry" fct in
      let builder = builder context in
      position_at_end entryb builder;

      (* grab the linked list in the heap *)
      let segmentsptrptr = build_gep heap_ptr [| zero; zero |] "segmentsptrptr" builder in
      let segmentsptr = build_load segmentsptrptr "segmentsptr" builder in

      (* creating a new segment *)
      let new_segmentptr = build_call memalign_ptr [| const_int size_type segment_max_size_bytes; const_int size_type segment_max_size_bytes |] "new_segmentptr" builder in
      let _ = build_call memset_ptr [| new_segmentptr; const_int size_type 0; const_int size_type segment_max_size_bytes |] "" builder in
      let new_segmentptr = build_bitcast new_segmentptr (pointer_type segment_header_type) "new_segmentptr" builder in

      (* introducing in the linked list *)
      let new_segmentptr_nextptrptr = build_gep new_segmentptr [| zero; one |] "new_segmentptr_nextptrptr" builder in
      
      (* set the next pointer of the new segment to the segment pointed by the heap *)
      let _ = build_store segmentsptr new_segmentptr_nextptrptr builder in
      
      (* set the segment pointed by the heap to the new segment *)
      let _ = build_store new_segmentptr segmentsptrptr builder in      

      let _ = build_ret_void builder in

      Llvm_analysis.assert_valid_function fct;
      if !optimize then ignore(PassManager.run_function fct pass_manager);
      fct
;;

let _ = create_Segment ();;

let _ = dump_module modul;;

open Mllvm;;
