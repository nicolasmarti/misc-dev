open Pycaml

open Def
open Interp

open Comp

let main () = 
  init_interp ();
  comp_init ();
  pymain Sys.argv;;

main ()
