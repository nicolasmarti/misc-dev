open Def
open Libpprinter
open Libparser
open Primitive

let float_type_uuid = get_fresh_uuid ();;

class floatTypeObj =
object (self)
  inherit [term, context, defs] tObj
  method uuid = float_type_uuid
  method get_name = "Float"
  method get_type = Type nopos
  method my_self = (self :> (term, context, defs) tObj)
  method pprint = (fun _ -> Verbatim self#get_name)
  method apply = fun defs context args -> raise (Failure "????")
  method equal = fun o ->
    if o#uuid = float_type_uuid then
      true
    else
      false	
end;;

let floatType = 
  let o = new floatTypeObj in
    Obj (o#my_self, nopos)
;;

let float_value_uuid = get_fresh_uuid ();;

(* The class for the term *)
class floatTermObj f =
object (self)
  inherit [term, context, defs] tObj
  val floatvalue = f
  method uuid = float_value_uuid
  method get_floatvalue = floatvalue
  method get_name = string_of_float floatvalue
  method get_type = floatType
  method equal = (fun o -> 
    if o#uuid = float_value_uuid then
      (((Obj.magic o) :> floatTermObj)#get_floatvalue = self#get_floatvalue)
    else
      false
  )
  method pprint = (fun _ -> Verbatim self#get_name)
  method apply = fun defs context args -> raise (Failure "????")
  method my_self = (self :> (term, context, defs) tObj)
end;;

let create_floatTerm f =
  let o = new floatTermObj f in
    Obj (o#my_self, nopos)
;;
