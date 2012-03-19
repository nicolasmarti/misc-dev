open Str
open Libparser
open Printf

let blank = whitespaces

let rg = regexp "[-a-zA-Z0-9\\.]+";;

let parse_elt : string parsingrule = applylexingrule (rg, 
						      fun (s:string) -> 
                                                        (*printf "parsed: %s\n" s; flush stdout;*)
						        s
)
;;


let parse_line : float parsingrule =
  fun pb ->
    let l = separatedBy parse_elt (word ",") pb in
    match l with
      | [bdate; bopen; bhigh; blow; bclose; bvolume; badjustclose] ->
        (*printf "l := [%s]\n" (String.concat ", " l); *)
        (float_of_string badjustclose)
      | _ -> printf "l := [%s]\n" (String.concat ", " l); raise NoMatch
;;

let parse_lines = 
  separatedBy parse_line whitespaces
;;

let parse_csv csv =
  let lines = stream_of_string csv in
  let pb = build_parserbuffer lines in
  try (
    let lines = parse_lines pb in
    printf "parsed %n lines\n" (List.length lines); flush stdout;
    lines
  ) with
    | NoMatch -> 
      printf "parsing error:=\n%s\n" (markerror pb);
      raise Pervasives.Exit
;;

open Finance_intf;;

module CSVBroker =
struct

  type status = RUNNING
		| STOPPED

  type t = {
    close: float list;
    mutable index: int;
    mutable st: status;
  };;

  type data = float list;;

  type info = string;;

  let init info = {close = List.rev (parse_csv info);
		   index = 0;
		   st = STOPPED;
		  };;

  let start t = t.st <- RUNNING;;
  let stop t = t.st <- STOPPED; t.index <- 0;;
  let getstatus t = t.st;;
  
  let rec take l n =
    match n with
      | 0 -> []
      | n -> 
	match l with
	  | [] -> []
	  | hd::tl -> hd::(take tl (n-1))
  ;;

  let getdata t = 
    if t.index >= List.length t.close then
      (t.st <- STOPPED; t.close)
    else
      let i = t.index in t.index <- t.index + 1; take t.close i
  ;;
  
  type order = int;;

  type orderId = int * int;;

  type orderRes = Filled
		  | Cancelled
		  | Pending
  ;;

  let mkOrder self f =
    int_of_float (f /. 
		    (try 
		       List.nth self.close self.index 
		     with
		       | _ -> List.nth self.close (List.length self.close - 1))
		    
    )
  ;;

  let proceedOrder t o = (t.index, o);;
  let orderStatus t oid = Filled;;
  let cancelOrder t oid = ();;
  let closeOrder t (index, o) = (t.index, -o);;
  let orderValue t (index, o) = 
    (try 
       List.nth t.close index 
     with
       | _ -> List.nth t.close (List.length t.close - 1)) *. float o;;

  let orderPnL t (index, o) = (
    (try 
       List.nth t.close t.index 
     with
       | _ -> List.nth t.close (List.length t.close - 1))
    -. 
      List.nth t.close index
  ) *. float o;;
  
end;;

