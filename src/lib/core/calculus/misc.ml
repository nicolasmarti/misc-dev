open Def
open Libparser

let empty_context = empty_frame::[]

let empty_defs () = { store = Hashtbl.create 30; hist = [] }

let copy_defs (defs: defs) = {defs with store = Hashtbl.copy defs.store}

(* returns the numbers of bvars introduced by a pattern 
   we should always have 
   pattern_size p = List.length (fst (pattern_bvars p)))
*)
let rec pattern_size (p: pattern) : int =
  match p with
    | PType _-> 0
    | PVar _ -> 1
    | PAVar _ -> 1
    | PCste _ -> 0
    | PAlias (_, p, _, _) -> 1 + pattern_size p
    | PApp (_, args, _, _) -> 
      List.fold_left ( fun acc (hd, _) -> acc + pattern_size hd) 0 args

(* set the outermost pattern type *)
let set_pattern_type (p: pattern) (ty: term) : pattern =
  match p with
    | PVar (n, _, pos) -> PVar (n, ty, pos)
    | PAVar (_, pos) -> PAVar (ty, pos)
    | PAlias (n, p, _, pos) -> PAlias (n, p, ty, pos)
    | PApp (s, args, _, pos) -> PApp (s, args, ty, pos)
    | _ -> p    

(* set the outermost pattern position *)
let set_pattern_pos (p: pattern) (pos: pos) : pattern =
  match p with
    | PType _ -> PType pos
    | PVar (n, ty, _) -> PVar (n, ty, pos)
    | PAVar (ty, _) -> PAVar (ty, pos)
    | PCste (s, _) -> PCste (s, pos)
    | PAlias (n, p, ty, _) -> PAlias (n, p, ty, pos)
    | PApp (s, args, ty, _) -> PApp (s, args, ty, pos)

(* get the outermost pattern position *)
let get_pattern_pos (p: pattern) : pos =
  match p with
    | PType pos -> pos
    | PVar (_, _, pos) -> pos
    | PAVar (_, pos) -> pos
    | PCste (_, pos) -> pos
    | PAlias (_, _, _, pos) -> pos
    | PApp (_, _, _, pos) -> pos

(* set the outermost term position *)
let set_term_pos (te: term) (p: pos) : term =
    match te with
      | Type _ -> Type p
      | Cste (s, _) -> Cste (s, p)
      | Obj (o, _) -> Obj (o, p)
      | TVar (i, _) -> TVar (i, p)
      | AVar _ -> AVar p
      | TName (s, _) -> TName (s, p)
      | App (f, args, _) -> App (f, args, p)
      | Impl (q, te, _) -> Impl (q, te, p)
      | Lambda (q, te, _) -> Lambda (q, te, p)
      | Match (te, eqs, _) -> Match (te, eqs, p)

(* set the outermost term position *)
let get_term_pos (te: term) : pos =
    match te with
      | Type p -> p
      | Cste (_, p) -> p
      | Obj (_, p) -> p
      | TVar (_, p) -> p
      | AVar p -> p
      | TName (_, p) -> p
      | App (_, _, p) -> p
      | Impl (_, _, p) -> p
      | Lambda (_, _, p) -> p
      | Match (_, _, p) -> p

(* the set of free variable in a term *)
let rec fv_term (te: term) : IndexSet.t =
  match te with
    | Type _ | Cste _ | Obj _ -> IndexSet.empty
    | TVar (i, _) when i >= 0 -> IndexSet.empty
    | TVar (i, _) when i < 0 -> IndexSet.singleton i
    | AVar _ -> IndexSet.empty
    | TName _ -> IndexSet.empty
    | App (te, args, _) ->
      List.fold_left (fun acc (te, _) -> IndexSet.union acc (fv_term te)) (fv_term te) args
    | Impl ((s, ty, n, pos), te, _) ->
      IndexSet.union (fv_term ty) (fv_term te)
    | Lambda ((s, ty, n, pos), te, _) ->
      IndexSet.union (fv_term ty) (fv_term te)
    | Match (te, eqs, _) ->
      List.fold_left (fun acc eq -> IndexSet.union acc (fv_equation eq)) (fv_term te) eqs

and fv_pattern (p: pattern) : IndexSet.t =
  match p with
    | PType _ | PCste _ -> IndexSet.empty
    | PVar (_, ty, _) -> fv_term ty
    | PAVar (ty, _) -> fv_term ty
    | PAlias (_, p, ty, _) -> IndexSet.union (fv_term ty) (fv_pattern p)
    | PApp (_, args, ty, _) ->
      List.fold_left (fun acc (p, _) -> IndexSet.union acc (fv_pattern p)) (fv_term ty) args

and fv_equation (eq: equation) : IndexSet.t =
  let p, te = eq in
  IndexSet.union (fv_pattern p) (fv_term te)

(* shift a set of variable *)
let shift_vars (vars: IndexSet.t) (delta: int) : IndexSet.t =
  IndexSet.fold (fun e acc ->
    if (e >= 0 && e + delta < 0) || e < 0 then acc
    else IndexSet.add (e + delta) acc      
  ) vars IndexSet.empty


(* the set of bound variable in a term *)
let rec bv_term (te: term) : IndexSet.t =
  match te with
    | Type _ | Cste _ | Obj _ -> IndexSet.empty
    | TVar (i, _) when i >= 0 -> IndexSet.singleton i
    | TVar (i, _) when i < 0 -> IndexSet.empty
    | AVar _ -> IndexSet.empty
    | TName _ -> IndexSet.empty
    | App (te, args, _) ->
      List.fold_left (fun acc (te, _) -> IndexSet.union acc (bv_term te)) (bv_term te) args
    | Impl ((s, ty, n, pos), te, _) ->
      IndexSet.union (bv_term ty) (shift_vars (bv_term te) (-1))
    | Lambda ((s, ty, n, pos), te, _) ->
      IndexSet.union (bv_term ty) (shift_vars (bv_term te) (-1))
    | Match (te, eqs, _) ->
      List.fold_left (fun acc eq -> IndexSet.union acc (bv_equation eq)) (bv_term te) eqs

and bv_pattern (p: pattern) : IndexSet.t =
  match p with
    | PType _ | PCste _ -> IndexSet.empty
    | PVar (_, ty, _) -> (shift_vars (bv_term ty) (-1))
    | PAVar (ty, _) -> (shift_vars (bv_term ty) (-1))
    | PAlias (_, p, ty, _) -> IndexSet.union (shift_vars (bv_term ty) (- (pattern_size p))) (bv_pattern p)
    | PApp (_, args, ty, _) ->
      let i, vars = List.fold_left (fun (i, acc) (p, _) ->
	i - pattern_size p, IndexSet.union acc (shift_vars (bv_pattern p) i)
      ) (0, IndexSet.empty) args in
      IndexSet.union vars (shift_vars (bv_term ty) i)

and bv_equation (eq: equation) : IndexSet.t =
  let p, te = eq in
  IndexSet.union (bv_pattern p) (shift_vars (bv_term te) (pattern_size p))

(* function that map symbol into string *)
let symbol2string (s: symbol) =
  match s with
    | Name n -> n
    | Symbol (n, o) ->
      let (pre, post) = 
	match o with
	  | Nofix -> "", ""
	  | Prefix _ -> "[", ")"
	  | Infix _ -> "(", ")"
	  | Postfix _ -> "(", "]"
      in
      String.concat "" [pre; n; post]

(* get a bound variable frame *)
let get_bvar_frame (ctxt: context) (i: index) : frame =
  try 
    List.nth ctxt i
  with
    | Failure _ -> raise (DoudouException (UnknownBVar (i, ctxt)))
    | Invalid_argument _ -> raise (DoudouException (NegativeIndexBVar i))

(*
  the priority of operators
  the greater, the more strongly binding
  Nofix have 0
*)
let op_priority (o: op) : int =
  match o with
    | Nofix -> 0
    | Prefix i -> i
    | Infix (i, _) -> i
    | Postfix i -> i

(* returns only the elements that are explicit *)
let filter_explicit (l: ('a * nature) list) : 'a list =
  List.map fst (List.filter (fun (_, n) -> n = Explicit) l)

(* utilities for DoudouException *)
(* build an implication: no shifting in types !!! *)
let build_impl (symbols: (symbol * pos) list) (ty: term) (nature: nature) (body: term) : term =
  List.fold_right (fun (s, pos) acc -> Impl ((s, ty, nature, pos), acc, (fst pos, snd (get_term_pos acc)))) symbols body

let build_impls (qs: ((symbol * pos) list * term * nature) list) (body: term) : term =
  List.fold_right (fun (s, ty, n) acc -> build_impl s ty n acc) qs body

(* build a Lambda: no shifting in types !!! *)
let build_lambda (symbols: (symbol * pos) list) (ty: term) (nature: nature) (body: term) : term =
  List.fold_right (fun (s, pos) acc -> Lambda ((s, ty, nature, pos), acc, (fst pos, snd (get_term_pos acc)))) symbols body

(* build a Lambda: no shifting in types !!! *)
let build_lambdas (qs: ((symbol * pos) list * term * nature) list) (body: term) : term =
  List.fold_right (fun (s, ty, n) acc -> build_lambda s ty n acc) qs body

(* recursive destrution of impl (with an optionally max number of quantifiers) and lambdas *)
let rec destruct_impl ?(nb_qs: int = -1) (ty: term) : (symbol * term * nature * pos) list * term =
  if nb_qs = 0 then [], ty else
  match ty with
    | Impl (e, te, _) ->
      let l, te = destruct_impl ~nb_qs:(nb_qs - 1) te in
      e::l, te
    | _ -> [], ty

let rec destruct_lambda (ty: term) : (symbol * term * nature * pos) list * term =
  match ty with
    | Lambda (e, te, _) ->
      let l, te = destruct_lambda te in
      e::l, te
    | _ -> [], ty

let rec construct_lambda (l: (symbol * term * nature * pos) list) (body: term) : term =
  match l with
    | [] -> body
    | hd :: tl -> Lambda (hd, construct_lambda tl body, nopos)

(* destruction of application *)
let rec destruct_app (te: term) : term * (term * nature) list =
  match te with
    (* we make sure the application are in normal forms *)
    | App (App (hd, args1, _), args2, _) ->
      destruct_app (App (hd, args1 @ args2, nopos))
    | App (hd, args, _) -> hd, args
    | _ -> te, []

(* this is the equality modulo position/app/... *)
let rec eq_term (te1: term) (te2: term) : bool =
  match te1, te2 with
    | Type _, Type _ -> true
    | Cste (s1, _), Cste (s2, _) -> s1 = s2
    | Obj (o1, _), Obj (o2, _) -> o1 = o2
    | TVar (i1, _), TVar (i2, _) -> i1 = i2
    | AVar _, AVar _ -> true
    | TName (s1, _), TName (s2, _) -> s1 = s2
    | Impl ((s1, ty1, n1, _), te1, _), Impl ((s2, ty2, n2, _), te2, _) ->
	s1 = s2 && eq_term ty1 ty2 && n1 = n2 && eq_term te1 te2
    | Lambda ((s1, ty1, n1, _), te1, _), Lambda ((s2, ty2, n2, _), te2, _) ->
      s1 = s2 && eq_term ty1 ty2 && n1 = n2 && eq_term te1 te2
    | App (te1, args1, _), App (te2, args2, _) when List.length args1 = List.length args2 ->
      List.fold_left (fun acc ((arg1, n1), (arg2, n2)) -> acc && n1 = n2 && eq_term arg1 arg2) (eq_term te1 te2) (List.combine args1 args2)
    | App (App (te1, args1,_), args1', _), _ ->
      eq_term (App (te1, args1 @ args1', nopos)) te2
    | _, App (App (te2, args2,_), args2', _) ->
      eq_term te1 (App (te2, args2 @ args2', nopos)) 
    | Match (te1, eqs1, _), Match (te2, eqs2, _) when List.length eqs1 = List.length eqs2 ->
      List.fold_left (fun acc (eq1, eq2) ->
	acc && eq_equation eq1 eq2
      ) (eq_term te1 te2) (List.combine eqs1 eqs2)
    | _ -> false
and eq_equation (eq1: equation) (eq2: equation) : bool =
  let p1, te1 = eq1 in
  let p2, te2 = eq2 in
  eq_pattern p1 p2 && eq_term te1 te2
and eq_pattern (p1: pattern) (p2: pattern) : bool =
    match p1, p2 with
      | PType _, PType _ -> true
      | PCste (s1, _), PCste (s2, _) -> s1 = s2
      | PVar (n1, ty1, _), PVar (n2, ty2, _) ->
	n1 = n2 && eq_term ty1 ty2
      | PAVar (ty1, _), PAVar (ty2, _) ->
	eq_term ty1 ty2
      | PAlias (n1, p1, ty1, _), PAlias (n2, p2, ty2, _) ->
	n1 = n2 && eq_pattern p1 p2 && eq_term ty1 ty2
      | PApp ((s1, _), args1, ty1, _), PApp ((s2, _), args2, ty2, _) when List.length args1 = List.length args2 ->
	List.fold_left (fun acc ((arg1, n1), (arg2, n2)) -> 
	  n1 = n2 && eq_pattern arg1 arg2
	) (s1 = s2 && eq_term ty1 ty2) (List.combine args1 args2)
      | _ -> false

(* build the set of names of the frames *)
let build_name_set (ctxt: context) : NameSet.t =
  List.fold_left (fun acc hd -> NameSet.add (symbol2string hd.symbol) acc) NameSet.empty ctxt

(* some name freshness *)
let rec add_string_index (y: string) index =
  let len = (String.length y - index) in
  match (String.get y) len with 
    | c when c >= '0' && c < '9' -> (String.set y len (char_of_int (int_of_char c + 1))); y 
    | '9' -> (String.set y len '0'); (add_string_index (y: string) (index + 1));
    | c -> (String.concat "" (y :: "0" :: [])) ;;

let rec fresh_name ?(basename: string = "H") (s: NameSet.t) : string =
  if NameSet.mem basename s then
    fresh_name ~basename:(add_string_index basename 1) s
  else
    basename

let rec fresh_name_context ?(basename: string = "H") (ctxt: context) : string =
  let nameset = build_name_set ctxt in
  fresh_name ~basename:basename nameset

(* build a new frame 
   value is optional
*)
let build_new_frame (s: symbol) ?(value: term = TVar (0, nopos)) ?(nature: nature = Explicit) ?(pos: pos = nopos) (ty: term) : frame =
{ 
  symbol = s;
  ty = ty;
  nature = nature;
  value = value;
  pos = pos;

  fvs = [];
  termstack = [];
  naturestack = [];
  patternstack = [];

  unifiable_terms = [];
}

