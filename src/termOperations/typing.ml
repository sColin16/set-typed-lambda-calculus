open Common.Helpers
open TermTypes
open Metatypes
open TypeOperations.Helpers
open TypeOperations.Create
open TypeOperations.Intersection
open TypeOperations.Subtype
open TypeOperations.Context
open TypeOperations.Union
open TypeOperations.SubstituteUnivVar

type var_type_env = recursive_type list

(** [type_lambda_term term] determines the type of a term, if it is well-typed *)
let rec get_type (term : term) = get_type_rec term []

and get_type_rec (term : term) (var_type_env : var_type_env) :
    recursive_type option =
  match term with
  (* Constants always have label types *)
  | Const name -> Some (label_type name)
  (* Use the helper function to determine if an application is well-typed *)
  | Application (t1, t2) ->
      let left_type = get_type_rec t1 var_type_env in
      let right_type = get_type_rec t2 var_type_env in
      flat_map_opt2 get_application_type left_type right_type
  (* Abstractions are well-typed if their argument types don't match
     The return types of the body can be inferred recursively from the argument type *)
  | Abstraction definitions ->
      (* An abstraction is ill-typed if any of its arguments intersect *)
      let arg_types = extract_first definitions in
      let arg_pairs = self_pairs arg_types in
      let disjoint_args =
        not
          (List.exists
             (fun (arg1, arg2) -> has_intersection arg1 arg2)
             arg_pairs)
      in
      if not disjoint_args then None
      else
        let arg_types = List.map (fun (arg_type, _) -> arg_type) definitions in
        let body_opt_types =
          List.map
            (fun (arg_type, body) ->
              let new_var_type_env = arg_type :: var_type_env in
              get_type_rec body new_var_type_env)
            definitions
        in
        let body_types_opt = opt_list_to_list_opt body_opt_types in
        Option.map
          (fun body_types -> unify_function_types arg_types body_types)
          body_types_opt
  (* The type of a variable is based on the type of the argument in the abstraction defining it *)
  | Variable var_num -> List.nth_opt var_type_env var_num
  (* Determine the type within the quantifier, then merge the recursive contexts and build the appropriate union type *)
  | UnivQuantifier inner_term ->
      let inner_type_opt = get_type_rec inner_term var_type_env in
      Option.map
        (fun inner_type ->
          build_recursive_type
            [ UnivQuantification inner_type.union ]
            inner_type.context)
        inner_type_opt
  | UnivApplication (inner_term, inner_type) ->
      let inner_term_type_opt = get_type_rec inner_term var_type_env in
      Option.join
        (Option.map
           (fun inner_term_type ->
             get_univ_application_type inner_term_type inner_type)
           inner_term_type_opt)

(** [get_application_type func_type arg_type] determines the resulting type of
    applying a term of type [arg_type] to a term of type [func_type], if
    the function can be applied to the argument *)
and get_application_type (func : recursive_type) (arg : recursive_type) :
    recursive_type option =
  (* Flatten the func type so only labels and intersection types remain *)
  let func_flat = flatten_union func.union func.context in
  (* The argument should be applicable to any function in the union, so acquire the type of applying the arg to each option *)
  let return_types_opt =
    List.map
      (fun func_option ->
        get_application_option_type (func_option, func.context) arg)
      func_flat
  in
  (* Aggregate the return types - if any of them were none, the application is not well-typed *)
  (* Return types that come back have context func.context, since abstractions determine their return types *)
  let return_types = opt_list_to_list_opt return_types_opt in
  (* Join all of the return types into a single union type, add the context *)
  Option.map
    (fun return_types_concrete ->
      build_recursive_type (List.flatten return_types_concrete) func.context)
    return_types

and get_application_option_type
    ((func_option, context1) : flat_base_type * recursive_context)
    (arg : recursive_type) : union_type option =
  match func_option with
  (* Label types, universal quantifications, and their variables cannot be applied *)
  | FLabel _ | FUnivTypeVar _ | FUnivQuantification _ -> None
  (* An application against a function type is well-typed if the function accepts at least as many arguments.
     The return type is the union of all return types that the argument might match with *)
  | FIntersection functions ->
      let func_params = extract_composite_args functions in
      let exhaustive_arg_coverage =
        is_subtype arg (build_recursive_type func_params context1)
      in
      if not exhaustive_arg_coverage then None
      else
        Some
          (List.fold_left
             (fun acc (func_arg, func_return) ->
               if has_intersection arg (build_recursive_type func_arg context1)
               then acc @ func_return
               else acc)
             [] functions)

and get_univ_application_type (quantifier : recursive_type)
    (type_arg : recursive_type) : recursive_type option =
  (* Flatten the func type to get rid of recursive types *)
  let quantifier_flat = flatten_union quantifier.union quantifier.context in
  (* The type argument is applicable to any universal quantification in the union, so determine the types resulting
     from applying the type argument to each universal quantification in the union *)
  let return_opt_types =
    List.map
      (fun quant_option ->
        get_univ_application_option_type
          (quant_option, quantifier.context)
          type_arg)
      quantifier_flat
  in
  (* Aggregate the return types - if any of them were none, the application is not well-typed *)
  let return_types_opt = opt_list_to_list_opt return_opt_types in
  (* Combine all of the recursive types, merging both the unions and and contexts *)
  Option.map (fun return_types -> type_union return_types) return_types_opt

and get_univ_application_option_type
    ((func_option, context1) : flat_base_type * recursive_context)
    (type_arg : recursive_type) : recursive_type option =
  match func_option with
  (* Only universal quantification can have type applications
     Universal type variables may be instantiated with quantification (assuming impredicativity)
     but it's not guaranteed *)
  | FLabel _ | FIntersection _ | FUnivTypeVar _ -> None
  (* If we had bounded quantification, we'd need to make sure the type argument provided is valid *)
  (* But for now, we just substitution in the inner type. The function handles shifting for us *)
  | FUnivQuantification inner_union_type ->
      (* Construct the complete inner type using the context *)
      let inner_type = build_recursive_type inner_union_type context1 in
      Some (substitute_univ_var_type type_arg inner_type)