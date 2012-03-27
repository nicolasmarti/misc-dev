open Def2
open Libpprinter
open Libparser
open Extlist

let rec withParen (t: token) : token =
  Box [Verbatim "("; t; Verbatim ")"]

let rec withBracket (t: token) : token =
  Box [Verbatim "{"; t; Verbatim "}"]

(* a data structure to mark the place where the term/pattern is *)
type place = InNotation of op * int (* in the sndth place of the application to the notation with op *)
	     | InApp (* in the head of application *)
	     | InArg of nature (* as an argument (Explicit) *)
	     | InAlias  (* in an alias pattern *)
	     | Alone (* standalone *)

(* pretty printing for errors *)
let pos2token (p: pos) : token option=
  match p with
    | ((-1, -1), (-1, -1)) -> None
    | (startp, endp) -> 
      Some (
	Box [Verbatim (string_of_int (fst startp)); 
	     Verbatim ":"; 
	     Verbatim (string_of_int (snd startp)); 
	     Verbatim "-"; 
	     Verbatim (string_of_int (fst endp)); 
	     Verbatim ":"; 
	     Verbatim (string_of_int (snd endp)); 
	    ]
      )

let with_position (t: token) (p: pos) : token =
  if flags.show_position then (
    match pos2token p with 
      | None -> t 
      | Some p -> Box [withParen t; Verbatim "@"; p]
  )
  else
    t

let with_universe (t: token) (u: universe) : token =
  if flags.show_position then
    Box [t; Verbatim "_"; Verbatim (string_of_int u)]
  else
    t

let sort2token (s: sort) : token =
  match s with
    | Set u -> with_universe (Verbatim "Set") u
    | Prop u -> with_universe (Verbatim "Prop") u
    | Type u -> with_universe (Verbatim "Type") u
;;

(*
let with_types (t: token) (ty: typeannotation) : token =
  (* first look if we show proof and if the typeannotation bears itself a Prop annotation *)
  if flags.show_proof = false && (match ty with | )

  let t1 = 
    if flags.show_typeannotation then
*)      

let rec term2token (ctxt: context) (te: term) (p: place): token =
  match te with
    | TSort (s, pos) ->
      with_position (sort2token s) pos
    | _ -> raise (Failure "term2token: not yet implemented")
;;

(* make a string from a term *)
let term2string (ctxt: context) (te: term) : string =
  let token = term2token ctxt te Alone in
  let box = token2box token 80 2 in
  box2string box
;;
