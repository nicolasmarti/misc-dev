open Llvm
open Llvm_executionengine
open Llvm_target
open Llvm_scalar_opts

open Mygc

let comp_init () =
  ignore (initialize_native_target ());
  gc_init ()
;;
