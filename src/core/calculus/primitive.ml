(*
  a file containging a registration mechanism for primitives implementation through objects
*)

open Def ;;

module UUIDSet = Set.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

let uuid_registry : UUIDSet.t = UUIDSet.empty;;

open Random;;

let get_fresh_uuid () =
  let id = ref (Random.int 10000000) in
  while UUIDSet.mem !id uuid_registry do
    id := Random.int 10000000
  done;
  !id;;
