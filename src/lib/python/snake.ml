open Pycaml;;

open Lang_intf;;
open Pylang;;
open Pycalculus;;

module PyLisp = PyLang(Lisplang.L);;
module PyCalculus = PyLang(Pycalculus.L);;

pymain Sys.argv;;

