open Def
open Interp
open Pycaml

let main () = 
  init_interp ();
  pymain Sys.argv;;

main ()
