open Metatypes
open GetContextShifts
open Create
open Common.Helpers

(** Shifts free universal type variables in a type by the shift amount *)
let rec shift_univ_var_type (rtype : recursive_type) (shift_amount : int) =
  shift_univ_var_type_rec shift_amount 0 rtype

and shift_univ_var_type_rec (shift_amount : int) (cutoff : int)
    (rtype : recursive_type) =
  (* Shift the universal type variables in the union type *)
  let shifted_union = shift_univ_var_union shift_amount cutoff rtype.union in
  (* Determine the shifts that need to be made to the recursive context *)
  let context_shifts =
    get_context_shifts { shift_amount; cutoff } rtype.union rtype.context
  in
  (* Shift the context accordingly *)
  let shifted_context = shift_univ_var_context rtype.context context_shifts in
  let shifted_type = build_recursive_type shifted_union shifted_context in
  shifted_type

and shift_univ_var_context (context : recursive_context)
    (context_shifts : context_shifts) =
  (* Shift each recursive definition with the appropriate directive (if any) *)
  List.mapi
    (fun idx context_def ->
      shift_univ_var_context_def context_def
        (IntMap.find_opt idx context_shifts))
    context

and shift_univ_var_context_def ({ kind; flat_union } : recursive_def)
    (shift_directive_opt : shift_directive option) =
  (* If the shift directive is None, then skip, otherwise shift the definition according to the directive *)
  if Option.is_none shift_directive_opt then { kind; flat_union }
  else
    let { shift_amount; cutoff } = Option.get shift_directive_opt in
    {
      kind;
      flat_union = shift_univ_var_flat_union shift_amount cutoff flat_union;
    }

and shift_univ_var_flat_union (shift_amount : int) (cutoff : int)
    (flat_union : flat_union_type) =
  List.map (shift_univ_var_flat_base shift_amount cutoff) flat_union

and shift_univ_var_flat_base (shift_amount : int) (cutoff : int)
    (flat_base : flat_base_type) =
  match flat_base with
  (* Labels don't need any shifting *)
  | FLabel _ -> flat_base
  (* Intersections are shifted recursively *)
  | FIntersection branches ->
      let shifted_branches =
        List.map (shift_univ_var_func shift_amount cutoff) branches
      in
      FIntersection shifted_branches
  (* When we cross through a quantifier, we increment the cutoff since the index of free variables
     increases by one as we pass through the quantifier *)
  | FUnivQuantification inner_type ->
      FUnivQuantification
        (shift_univ_var_union shift_amount (cutoff + 1) inner_type)
  (* Universal type variables are shifted if they are at least the cutoff value, which means they are free variables *)
  | FUnivTypeVar num ->
      if num >= cutoff then FUnivTypeVar (num + shift_amount)
      else FUnivTypeVar num

and shift_univ_var_union (shift_amount : int) (cutoff : int)
    (union : union_type) =
  List.map (shift_univ_var_base shift_amount cutoff) union

and shift_univ_var_base (shift_amount : int) (cutoff : int) (base : base_type) =
  match base with
  (* Labels and recursive type variables don't need to be shifted (recursive shifting happens in other step) *)
  | Label _ | RecTypeVar _ -> base
  (* Intersections are shifted recursively *)
  | Intersection branches ->
      let shifted_branches =
        List.map (shift_univ_var_func shift_amount cutoff) branches
      in
      Intersection shifted_branches
  (* When we cross through a quantifier, we increment the cutoff since the index of free variables
     increases by one as we pass through the quantifier *)
  | UnivQuantification inner_type ->
      UnivQuantification
        (shift_univ_var_union shift_amount (cutoff + 1) inner_type)
  (* Universal type variables are shifted if they are at least the cutoff value, which means they are free variables *)
  | UnivTypeVar num ->
      if num >= cutoff then UnivTypeVar (num + shift_amount)
      else UnivTypeVar num

and shift_univ_var_func (shift_amount : int) (cutoff : int)
    ((arg, return) : unary_function) =
  map_pair (shift_univ_var_union shift_amount cutoff) (arg, return)
