open Pycaml;;
open Printf;;
open Libparser;;
open Lang_intf;;
open Pylang;;

module PyLisp = PyLang(Lisplang.L);;

pymain Sys.argv;;

