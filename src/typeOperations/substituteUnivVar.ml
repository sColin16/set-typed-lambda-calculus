open Metatypes
open ShiftUnivVar
open Create
open Common.Helpers
open Context
open Helpers

module IntSet = Set.Make (struct
  type t = int

  let compare = compare
end)

module IntMap = Map.Make (struct
  type t = int

  let compare = compare
end)

type context_subs = int IntMap.t
(** Maps a recursive variable number to the base variable number to substitute in that recursive definition *)

type sub_mapping = recursive_type IntMap.t
(** Maps a universal type variable to the corresponding type that will substitute it *)

type substitution_profile = {
  (* All universal type numbers we are targeting to substitute, across quantifier "levels" *)
  targets : IntSet.t;
  (* Describes the universal type variable that we aim to subsitute for each recursive type variable *)
  context_subs : context_subs;
}

(** Describes a substitution, which we use to handle the complexity of recursive contexts before performing substitutions *)
let rec substitute_univ_var_type (with_type : recursive_type)
    (in_type : recursive_type) : recursive_type =
  (* Shift the free universal type variables in the with type by one, since they are about to be substituted into a universal quantification,
     where their binding quantification is further away *)
  let shifted_with_type = shift_univ_var_type with_type 1 in
  (* Perform the substitution on universal quantification variables bound to this outermost universal quantification *)
  let substitution_result =
    substitute_univ_var_type_rec 0 shifted_with_type in_type
  in
  (* Finally, shift all the free universal type variables down one since we can now remove the outermost universal quantification,
     and so all free universal type variables move one closer to their binding quantifier *)
  let final_result = shift_univ_var_type substitution_result (-1) in
  final_result

(** Substitutes universal type variables with the given number in the in_type
    with the with_type, respecting free variables and the complexities of recursive
    types *)
and substitute_univ_var_type_rec (variable_num : int)
    (with_type : recursive_type) (in_type : recursive_type) : recursive_type
    =
  (* Perform initial pass over substitution to get information we use to safely perform substitution *)
  let substitution_profile = get_substitution_profile variable_num in_type in

  (* Get the initial map from univeral type number to the corresponding with type, obtained via shifting the with_type *)
  let initial_sub_mapping =
    get_initial_sub_mapping variable_num with_type substitution_profile.targets
  in

  (* Unify the type contexts across the in_type and all the with_types in the sub mapping *)
  let unified_in_type, unified_sub_mapping =
    unify_sub_mapping in_type initial_sub_mapping
  in

  (* TODO: we could consider skipping this step if we already determined no substitutions are needed *)
  (* Perform the substitution in the union type, with the safe substitution directives *)
  let substituted_union =
    substitute_univ_union variable_num unified_sub_mapping unified_in_type.union
  in

  (* Perform the substitution in the context, with the safe substitution directives, and the profile defining which variable numbers receive which substitution *)
  let substituted_context =
    substitute_univ_context substitution_profile.context_subs
      unified_sub_mapping unified_in_type.context
  in
  build_recursive_type substituted_union substituted_context

and get_substitution_profile (variable_num : int) (in_type : recursive_type) :
    substitution_profile =
  let context_subs = get_context_subs variable_num in_type in
  let all_targets = get_targets variable_num context_subs in_type in
  { targets = all_targets; context_subs }

and get_context_subs (variable_num : int) (in_type : recursive_type) =
  let initial_subs = get_context_subs_union variable_num in_type.union in
  let final_subs = get_context_subs_context initial_subs in_type.context in
  final_subs

and get_context_subs_union (variable_num : int) (union_type : union_type) =
  map_context_subs get_context_subs_base variable_num union_type

and get_context_subs_base (variable_num : int) (base_type : base_type) =
  match base_type with
  | Label _ | UnivTypeVar _ -> IntMap.empty
  | RecTypeVar num -> IntMap.singleton num variable_num
  | Intersection branches ->
      map_context_subs get_context_subs_func variable_num branches
  | UnivQuantification inner_type ->
      get_context_subs_union (variable_num + 1) inner_type

and get_context_subs_func (variable_num : int) ((arg, return) : unary_function)
    =
  let arg_subs, return_subs =
    map_pair (get_context_subs_union variable_num) (arg, return)
  in
  merge_context_subs_binary arg_subs return_subs

and get_context_subs_context (initial_subs : context_subs)
    (context : recursive_context) =
  get_context_subs_context_rec initial_subs initial_subs context

and get_context_subs_context_rec (acc_subs : context_subs)
    (new_subs : context_subs) (context : recursive_context) : context_subs =
  if IntMap.is_empty new_subs then acc_subs
  else
    let resulting_subs =
      merge_context_subs
        (List.map
           (fun (rec_num, univ_num) ->
             get_context_subs_rec_def univ_num (List.nth context rec_num))
           (IntMap.to_list new_subs))
    in
    let updated_new_subs = resolve_new_subs acc_subs resulting_subs in
    let updated_acc_subs =
      merge_context_subs_binary acc_subs updated_new_subs
    in
    get_context_subs_context_rec updated_acc_subs updated_new_subs context

and get_context_subs_rec_def (variable_num : int)
    ({ flat_union; _ } : recursive_def) =
  get_context_subs_flat_union variable_num flat_union

and get_context_subs_flat_union (variable_num : int)
    (flat_union : flat_union_type) =
  map_context_subs get_context_subs_flat_base variable_num flat_union

and get_context_subs_flat_base (variable_num : int) (flat_base : flat_base_type)
    =
  match flat_base with
  | FLabel _ | FUnivTypeVar _ -> IntMap.empty
  | FIntersection branches ->
      map_context_subs get_context_subs_func variable_num branches
  | FUnivQuantification inner_type ->
      get_context_subs_union (variable_num + 1) inner_type

and get_targets (variable_num : int) (context_sub_directives : context_subs)
    (in_type : recursive_type) =
  let union_targets = get_union_targets variable_num in_type.union in
  let context_targets =
    get_context_targets context_sub_directives in_type.context
  in
  IntSet.union union_targets context_targets

and resolve_new_subs (acc_subs : context_subs) (new_subs : context_subs) =
  IntMap.merge
    (fun _ acc_value new_value ->
      match (acc_value, new_value) with None, Some _ -> new_value | _ -> None)
    acc_subs new_subs

and get_union_targets (variable_num : int) (union_type : union_type) : IntSet.t
    =
  let base_targets_list = List.map (get_base_targets variable_num) union_type in
  union_sets base_targets_list

and get_base_targets (variable_num : int) (base_type : base_type) : IntSet.t =
  match base_type with
  | Label _ | RecTypeVar _ -> IntSet.empty
  | UnivTypeVar num ->
      if num = variable_num then IntSet.singleton num else IntSet.empty
  | Intersection branches ->
      let branch_targets = List.map (get_func_targets variable_num) branches in
      union_sets branch_targets
  | UnivQuantification inner_type ->
      get_union_targets (variable_num + 1) inner_type

and get_func_targets (variable_num : int) ((arg, return) : unary_function) :
    IntSet.t =
  let arg_targets, return_targets =
    map_pair (get_union_targets variable_num) (arg, return)
  in
  IntSet.union arg_targets return_targets

and get_context_targets (context_sub_directives : context_subs)
    (context : recursive_context) =
  IntMap.fold
    (fun rec_type_num univ_num_target context_targets ->
      let context_def = List.nth context rec_type_num in
      let context_def_targets =
        get_context_def_targets univ_num_target context_def
      in
      IntSet.union context_targets context_def_targets)
    context_sub_directives IntSet.empty

and get_context_def_targets (variable_num : int)
    ({ flat_union; _ } : recursive_def) =
  get_flat_union_targets variable_num flat_union

and get_flat_union_targets (variable_num : int) (flat_union : flat_union_type) =
  let base_targets_list =
    List.map (get_flat_base_targets variable_num) flat_union
  in
  union_sets base_targets_list

and get_flat_base_targets (variable_num : int) (flat_base : flat_base_type) =
  match flat_base with
  | FLabel _ -> IntSet.empty
  | FUnivTypeVar num ->
      if num = variable_num then IntSet.singleton num else IntSet.empty
  | FIntersection branches ->
      let branch_targets = List.map (get_func_targets variable_num) branches in
      union_sets branch_targets
  | FUnivQuantification inner_type ->
      get_union_targets (variable_num + 1) inner_type

and get_initial_sub_mapping (variable_num : int) (with_type : recursive_type)
    (targets : IntSet.t) : sub_mapping =
  let bindings =
    List.map
      (fun target ->
        (target, shift_univ_var_type with_type (target - variable_num)))
      (IntSet.to_list targets)
  in
  IntMap.of_list bindings

and unify_sub_mapping (in_type : recursive_type)
    (initial_sub_mapping : sub_mapping) =
  let sub_mapping_with_types =
    extract_second (IntMap.to_list initial_sub_mapping)
  in
  match get_unified_type_context (in_type :: sub_mapping_with_types) with
  | new_in_type_union :: new_sub_mapping_with_union_types, new_context ->
      let new_in_type = build_recursive_type new_in_type_union new_context in
      let new_sub_mapping_with_types =
        List.map
          (fun union_type -> build_recursive_type union_type new_context)
          new_sub_mapping_with_union_types
      in
      let new_sub_mapping_bindings =
        List.mapi
          (fun idx (univ_variable, _) ->
            let new_with_type = List.nth new_sub_mapping_with_types idx in
            (univ_variable, new_with_type))
          (IntMap.to_list initial_sub_mapping)
      in
      let new_sub_mapping = IntMap.of_list new_sub_mapping_bindings in
      (new_in_type, new_sub_mapping)
  | _ -> raise (Failure "Failed to destructure substitution unification")

and substitute_univ_union (variable_num : int) (sub_mapping : sub_mapping)
    (union_type : union_type) =
  List.flatten
    (List.map (substitute_univ_base variable_num sub_mapping) union_type)

and substitute_univ_base (variable_num : int) (sub_mapping : sub_mapping)
    (base_type : base_type) : union_type =
  match base_type with
  | Label _ | RecTypeVar _ -> [ base_type ]
  | Intersection branches ->
      let substituted_branches =
        List.map (substitute_univ_func variable_num sub_mapping) branches
      in
      [ Intersection substituted_branches ]
  | UnivTypeVar num ->
      if num = variable_num then (IntMap.find num sub_mapping).union
      else [ UnivTypeVar num ]
  | UnivQuantification inner_type ->
      [
        UnivQuantification
          (substitute_univ_union (variable_num + 1) sub_mapping inner_type);
      ]

and substitute_univ_func (variable_num : int) (sub_mapping : sub_mapping)
    ((arg, return) : unary_function) =
  map_pair (substitute_univ_union variable_num sub_mapping) (arg, return)

and substitute_univ_context (context_sub_directives : context_subs)
    (sub_mapping : sub_mapping) (context : recursive_context) =
  List.mapi
    (fun idx context_def ->
      substitute_univ_context_def
        (IntMap.find_opt idx context_sub_directives)
        sub_mapping context_def)
    context

and substitute_univ_context_def (variable_num_opt : int option)
    (sub_mapping : sub_mapping) (recursive_def : recursive_def) =
  match variable_num_opt with
  | None -> recursive_def
  | Some variable_num ->
      {
        recursive_def with
        flat_union =
          substitute_univ_flat_union variable_num sub_mapping
            recursive_def.flat_union;
      }

and substitute_univ_flat_union (variable_num : int) (sub_mapping : sub_mapping)
    (flat_union : flat_union_type) =
  List.flatten
    (List.map (substitute_univ_flat_base variable_num sub_mapping) flat_union)

and substitute_univ_flat_base (variable_num : int) (sub_mapping : sub_mapping)
    (flat_base : flat_base_type) =
  match flat_base with
  | FLabel _ -> [ flat_base ]
  | FIntersection branches ->
      let substituted_branches =
        List.map (substitute_univ_func variable_num sub_mapping) branches
      in
      [ FIntersection substituted_branches ]
  | FUnivTypeVar num ->
      if num = variable_num then
        let with_type = IntMap.find num sub_mapping in
        let flat_with_type = flatten_union with_type.union with_type.context in
        flat_with_type
      else [ FUnivTypeVar num ]
  | FUnivQuantification inner_type ->
      [
        FUnivQuantification
          (substitute_univ_union (variable_num + 1) sub_mapping inner_type);
      ]

and map_context_subs :
      'a. (int -> 'a -> context_subs) -> int -> 'a list -> context_subs =
 fun func variable_num list ->
  let substitutions = List.map (func variable_num) list in
  merge_context_subs substitutions

and union_sets (sets : IntSet.t list) =
  List.fold_left IntSet.union IntSet.empty sets

and merge_context_subs (directives : context_subs list) =
  List.fold_left merge_context_subs_binary IntMap.empty directives

and merge_context_subs_binary (directives_a : context_subs)
    (directives_b : context_subs) =
  IntMap.merge
    (fun _ left_val right_val ->
      match (left_val, right_val) with
      (* TODO: consider throwing an exception here on mismatch to detect recursive type variables used across levels *)
      | Some x, Some _ -> Some x
      | None, y -> y
      | x, None -> x)
    directives_a directives_b