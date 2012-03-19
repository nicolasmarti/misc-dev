
type datetime = {
  year: int;
  mounth: int;
  day: int;
  hour: int;
  minute: int;
  second: int;
  tz: string;
};;

let int2string (i: int) (size: int) : string =
  let s = string_of_int i in
  if String.length s > size then
    raise (Failure "int2string: string rep. to long")
  else
    if String.length s < size then (
      let prefix = String.make (size - String.length s) '0' in
      String.concat "" [prefix; s]
    ) else s
;;

open Libparser;;

(*
  parser for format
  
  yyyymmdd{space}{space}hh:mm:dd
*)

let num_parser: string parsingrule =
  one_of ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"]
;;

let rec datetime_parser: datetime parsingrule =
  fun pb ->
    let y0 = num_parser pb in
    let y1 = num_parser pb in
    let y2 = num_parser pb in
    let y3 = num_parser pb in
    let mo0 = num_parser pb in
    let mo1 = num_parser pb in
    let d0 = num_parser pb in
    let d1 = num_parser pb in
    let () = word " " pb in
    let () = word " " pb in
    let h0 = num_parser pb in
    let h1 = num_parser pb in
    let () = word ":" pb in
    let mi0 = num_parser pb in
    let mi1 = num_parser pb in
    let () = word ":" pb in
    let s0 = num_parser pb in
    let s1 = num_parser pb in

    {
      year = int_of_string (String.concat "" [y0; y1; y2; y3]);
      mounth = int_of_string (String.concat "" [mo0; mo1]);
      day = int_of_string (String.concat "" [d0; d1]);
      hour = int_of_string (String.concat "" [h0; h1]);
      minute = int_of_string (String.concat "" [mi0; mi1]);
      second = int_of_string (String.concat "" [s0; s1]);
      tz = "";
    }
and parse_datetime (str: string) : datetime =
  let lines = stream_of_string str in
  let pb = build_parserbuffer lines in
  datetime_parser pb
;;


(*
  transform a datetime into the following format 
  yyyymmdd HH:mm:ss ttt

  (ttt being optional)
*)  
let datetime_to_string (dt: datetime) : string =
  let year = int2string dt.year 4 in
  let mounth = int2string dt.mounth 2 in
  let day = int2string dt.day 2 in

  let date = String.concat "" [year; mounth; day] in

  let hour = int2string dt.hour 2 in
  let min = int2string dt.minute 2 in
  let sec = int2string dt.second 2 in

  let time = String.concat ":" [hour; min; sec] in

  let tz = if dt.tz = "" then [] else [dt.tz] in

  String.concat " " ([date; time] @ tz)
;;
  
type duration = Second of int
		| Day of int
		| Week of int
;;

let duration2string (d: duration) : string =
  match d with
    | Second i -> String.concat " " [string_of_int i; "S"]
    | Day i -> String.concat " " [string_of_int i; "D"]
    | Week i -> String.concat " " [string_of_int i; "W"]
;;

type barSize = SEC1
	       | SEC5
	       | SEC15
	       | SEC30
	       | MIN1
	       | MIN2
	       | MIN3
	       | MIN5
	       | MIN15
	       | MIN30
	       | HOUR1
	       | DAY1
;;

let barSize2string (bs: barSize) : string =
  match bs with
    | SEC1 -> "1 sec"
    | SEC5 -> "5 sec"
    | SEC15 -> "15 sec"
    | SEC30 -> "30 sec"
    | MIN1 -> "1 min"
    | MIN2 -> "2 mins"
    | MIN3 -> "3 mins"
    | MIN5 -> "5 mins"
    | MIN15 -> "15 mins"
    | MIN30 -> "30 mins"
    | HOUR1 -> "1 hour"
    | DAY1 -> "1 day"
;;
      
let diff_datetime (d1: datetime) (d2: datetime): duration =
  Second 0;;
(*
  raise (Failure "NYI");;
*)

let now (): datetime = {
  year = 0;
  mounth = 0;
  day = 0;
  hour = 0;
  minute = 0;
  second = 0;
  tz = "";
};;
