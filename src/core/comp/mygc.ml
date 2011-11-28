open Llvm
open Llvm_executionengine
open Llvm_target
open Llvm_scalar_opts

let gc_init () = 
    ignore (initialize_native_target ());;
