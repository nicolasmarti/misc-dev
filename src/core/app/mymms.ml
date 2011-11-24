open Def
open Interp
open Opycaml.Api

let main () = 
  Base.initialize ();
  init_interp ();  
  ignore (Base.main []);
  Base.finalize ();;

main ()
