open Def2;;
open Pprinter2;;
open Libpprinter;;
open Libparser;;
open Printf;;

let t1 = TSort (Set 0, nopos);;

let _ = printf "%s\n" (term2string [] t1);;
