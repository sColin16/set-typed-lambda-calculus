open Metatypes
open Common.Helpers

type shift_directive = { shift_amount : int; cutoff : int }

module IntMap = Map.Make (struct
  type t = int

  let compare = compare
end)

type context_shifts = shift_directive IntMap.t

(* Determines the shift directives for the recursive context, based on shifting the type as specified *)
let rec get_context_shifts (directive : shift_directive) (union : union_type)
    (context : recursive_context) =
  (* Determine the initial recursive variables to shift *)
  let initial_shifts = get_context_shifts_union directive union in
  (* Determine the remaining shifts that occur by shifting the recursive variable definitions *)
  let final_shifts = get_context_shifts_context initial_shifts context in
  final_shifts

and get_context_shifts_union (directive : shift_directive) (union : union_type)
    =
  map_context_shifts get_context_shifts_base directive union

and get_context_shifts_base (directive : shift_directive)
    (base_type : base_type) =
  match base_type with
  (* Recursive type variables indicate that their definitions must be shifted *)
  | RecTypeVar num -> IntMap.singleton num directive
  (* Labels and universal type variables don't indicate any shifts need to be made *)
  | Label _ | UnivTypeVar _ -> IntMap.empty
  (* Intersections may have shifts internally *)
  | Intersection branches ->
      map_context_shifts get_context_shifts_func directive branches
  (* When we cross through a quantifier, we increment the cutoff since the index
      of free variables increases by one as we pass through the quantifier *)
  | UnivQuantification inner_type ->
      get_context_shifts_union
        { directive with cutoff = directive.cutoff + 1 }
        inner_type

and get_context_shifts_func (directive : shift_directive)
    ((arg, return) : unary_function) =
  let arg_shifts, return_shifts =
    map_pair (get_context_shifts_union directive) (arg, return)
  in
  join_context_shift_binary arg_shifts return_shifts

(* Determines the context shifts that should occur as a result of of the initial shifts, including the initial shifts *)
and get_context_shifts_context (initial_shifts : context_shifts)
    (context : recursive_context) =
  get_context_shifts_context_rec initial_shifts initial_shifts context

(* Determines the context shifts that come from a set of new shifts *)
and get_context_shifts_context_rec (acc_shifts : context_shifts)
    (new_shifts : context_shifts) (context : recursive_context) : context_shifts
    =
  (* Base case: when we no longer have new shifts to perform, we use the shifts we've accumulated so far *)
  if IntMap.is_empty new_shifts then acc_shifts
  else
    (* Determine the shift for each recursive defintion that has a directive *)
    let resulting_shifts =
      join_context_shifts
        (List.map
           (fun (num, directive) ->
             get_context_shifts_rec_def (List.nth context num) directive)
           (IntMap.to_list new_shifts))
    in
    (* Determine the new shifts that weren't already part of the accumulated shifts *)
    let updated_new_shifts = resolve_new_shifts acc_shifts resulting_shifts in
    (* Determine the new set of accumulated shifts *)
    let updated_acc_shifts =
      join_context_shift_binary acc_shifts updated_new_shifts
    in
    (* Recursively call to get the rest of the shifts taht results from the new shifts *)
    get_context_shifts_context_rec updated_acc_shifts updated_new_shifts context

and get_context_shifts_rec_def ({ flat_union; _ } : recursive_def)
    (directive : shift_directive) =
  get_context_shifts_flat_union directive flat_union

and get_context_shifts_flat_union (directive : shift_directive)
    (flat_union : flat_union_type) =
  map_context_shifts get_context_shifts_flat_base directive flat_union

and get_context_shifts_flat_base (directive : shift_directive)
    (flat_base : flat_base_type) =
  match flat_base with
  (* Labels and type variables do not indicate shifts need to happen *)
  | FLabel _ | FUnivTypeVar _ -> IntMap.empty
  (* Intersection shifts are determined recursively *)
  | FIntersection branches ->
      map_context_shifts get_context_shifts_func directive branches
  (* When we cross through a quantifier, we increment the cutoff since the index
     of free variables increases by one as we pass through the quantifier *)
  | FUnivQuantification inner_type ->
      get_context_shifts_union
        { directive with cutoff = directive.cutoff + 1 }
        inner_type

(* Determines the shifts that are in new_shifts that aren't already in acc_shifts.
   Assumes that shifts to variables will be the same if repeated. Behavior is indeterminate otherwise *)
and resolve_new_shifts (acc_shifts : context_shifts)
    (new_shifts : context_shifts) =
  IntMap.merge
    (fun _ acc_value new_value ->
      match (acc_value, new_value) with
      (* Only pull out values for keys that are in the new_shifts, but not the acc_shifts *)
      | None, Some _ -> new_value
      | _ -> None)
    acc_shifts new_shifts

(* Applies a function that maps a shift directive and a type to the context
    shifts for that type, across a list of types *)
and map_context_shifts :
      'a.
      (shift_directive -> 'a -> context_shifts) ->
      shift_directive ->
      'a list ->
      context_shifts =
 fun func directive list ->
  let shifts = List.map (func directive) list in
  join_context_shifts shifts

(* Transforms a list of context shift maps into a single context shift map.
   Assumes maps context shifts contain identical shifts for a variable. Recursive variables
   that simultaneously have different shift directives have indeterminate behavior *)
and join_context_shifts (context_shifts : context_shifts list) : context_shifts
    =
  List.fold_left join_context_shift_binary IntMap.empty context_shifts

and join_context_shift_binary (context_shift_a : context_shifts)
    (context_shift_b : context_shifts) : context_shifts =
  IntMap.merge
    (fun _ left_val right_val ->
      match (left_val, right_val) with
      (* NOTE: we assume that shifts in both maps are identical. Behavior is indeterminate otherwise *)
      | Some x, Some _ -> Some x
      | None, y -> y
      | x, None -> x)
    context_shift_a context_shift_b
