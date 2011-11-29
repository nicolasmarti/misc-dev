open Def
open Libpprinter
open Libparser
open Primitive

let float_uuid = get_fresh_uuid ();;

class floatTypeObj =
object (self)
  inherit [term, context, defs] tObj
  method uuid = float_uuid
  method get_name = "Float"
  method get_type = Type nopos
  method my_self = (self :> (term, context, defs) tObj)
  method pprint = (fun _ -> Verbatim self#get_name)
  method apply = fun defs context args -> raise (Failure "????")
  method equal = fun o ->
    if o#uuid = float_uuid then
      true
    else
      false	
end;;

let floatType = 
  let o = new floatTypeObj in
    Obj (o#my_self, nopos)
;;

