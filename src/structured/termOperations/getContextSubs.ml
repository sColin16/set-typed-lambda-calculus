open Metatypes
open ShiftUnivVar

type substitute_directive = { variable_num : int; with_type : structured_type }

module IntMap = Map.Make (struct
  type t = int

  let compare = compare
end)

type context_subs = substitute_directive IntMap.t

(* Determines the substitution directives for the recursive context, based on
    the substitutions that are applied to the union type *)
let rec get_context_substitutions (directive : substitute_directive)
    (union : union_type) (context : recursive_context) =
  (* Determine the initial recursive variables to substitute *)
  let initial_subs = get_context_subs_union directive union in
  (* Determine the remaining substitutions that occur by shifting the recursive
      variable definitions *)
  let final_subs = get_context_subs_context initial_subs context in
  final_subs

and get_context_subs_union (directive : substitute_directive)
    (union : union_type) =
  map_context_subs get_context_subs_base directive union

and get_context_subs_base (directive : substitute_directive)
    (base_type : base_type) =
  match base_type with
  | RecTypeVar num -> IntMap.singleton num directive
  | Label _ | UnivTypeVar _ -> IntMap.empty
  | Intersection branches ->
      map_context_subs get_context_subs_func directive branches
  | UnivQuantification inner_type ->
      let new_var_num = directive.variable_num + 1 in
      let new_with_type = shift_univ_var_type directive.with_type 1 in
      get_context_subs_union
        { variable_num = new_var_num; with_type = new_with_type }
        inner_type

and get_context_subs_func (directive : substitute_directive)
    ((arg, return) : unary_function) =
  let arg_subs = get_context_subs_union directive arg in
  let return_subs = get_context_subs_union directive return in
  join_context_sub_binary arg_subs return_subs

(* Determines the context substitution that should occur as a result of the
    initial substitutions *)
and get_context_subs_context (initial_subs : context_subs)
    (context : recursive_context) =
  get_context_subs_context_rec initial_subs initial_subs context

and get_context_subs_context_rec (acc_subs : context_subs)
    (new_subs : context_subs) (context : recursive_context) : context_subs =
  if IntMap.is_empty new_subs then acc_subs
  else
    let resulting_subs =
      join_context_subs
        (List.map
           (fun (num, directive) ->
             get_context_subs_rec_def (List.nth context num) directive)
           (IntMap.to_list new_subs))
    in
    let updated_new_subs = resolve_new_subs acc_subs resulting_subs in
    let updated_acc_subs = join_context_sub_binary acc_subs updated_new_subs in
    get_context_subs_context_rec updated_acc_subs updated_new_subs context

and get_context_subs_rec_def ({ flat_union; _ } : recursive_def)
    (directive : substitute_directive) =
  get_context_subs_flat_union directive flat_union

and get_context_subs_flat_union (directive : substitute_directive)
    (flat_union : flat_union_type) =
  map_context_subs get_context_subs_flat_base directive flat_union

and get_context_subs_flat_base (directive : substitute_directive)
    (flat_base : flat_base_type) =
  match flat_base with
  | FLabel _ | FUnivTypeVar _ -> IntMap.empty
  | FIntersection branches ->
      map_context_subs get_context_subs_func directive branches
  | FUnivQuantification inner_type ->
      let new_var_num = directive.variable_num + 1 in
      let new_with_type = shift_univ_var_type directive.with_type 1 in
      get_context_subs_union
        { variable_num = new_var_num; with_type = new_with_type }
        inner_type

and resolve_new_subs (acc_subs : context_subs) (new_subs : context_subs) =
  IntMap.merge
    (fun _ acc_value new_value ->
      match (acc_value, new_value) with None, Some _ -> new_value | _ -> None)
    acc_subs new_subs

and map_context_subs :
      'a.
      (substitute_directive -> 'a -> context_subs) ->
      substitute_directive ->
      'a list ->
      context_subs =
 fun func directive list ->
  let substitutions = List.map (func directive) list in
  join_context_subs substitutions

and join_context_subs (context_subs : context_subs list) : context_subs =
  List.fold_left join_context_sub_binary IntMap.empty context_subs

and join_context_sub_binary (context_sub_a : context_subs)
    (context_sub_b : context_subs) : context_subs =
  IntMap.merge
    (fun _ left_val right_val ->
      match (left_val, right_val) with
      | Some x, Some _ -> Some x
      | None, y -> y
      | x, None -> x)
    context_sub_a context_sub_b
