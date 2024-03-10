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
open TypeOperations.MapType

type var_type_env = recursive_type list

(** [type_lambda_term term] determines the type of a term, if it is well-typed *)
let rec get_type (term : term) = get_type_rec term []

and get_type_rec (term : term) (var_type_env : var_type_env) :
    recursive_type option =
  match term with
  (* Constants always have label types *)
  | Const name -> Some (label_type name)
  (* The type of a variable is based on the type of the argument in the abstraction defining it *)
  | Variable var_num -> List.nth_opt var_type_env var_num
  | Application (t1, t2) ->
      let left_type = get_type_rec t1 var_type_env in
      let right_type = get_type_rec t2 var_type_env in
      flat_map_opt2 get_application_type left_type right_type
  | Abstraction branches ->
      (* An abstraction is ill-typed if any of its arguments intersect *)
      let branches_disjoint = abstraction_branches_disjoint branches in
      if not branches_disjoint then None
      else get_abstraction_type var_type_env branches
  | UnivApplication (inner_term, inner_type) ->
      let inner_term_type_opt = get_type_rec inner_term var_type_env in
      Option.bind inner_term_type_opt (fun inner_term_type ->
          get_univ_application_type inner_term_type inner_type)
  (* Determine the type within the quantifier, then nest the type inside the quantifier type *)
  | UnivQuantifier inner_term ->
      let inner_type_opt = get_type_rec inner_term var_type_env in
      Option.map
        (fun inner_type ->
          map_type
            (fun inner_type_union -> [ UnivQuantification inner_type_union ])
            inner_type)
        inner_type_opt

(** [get_application_type abs_type arg_type] determines the resulting type of
    applying a term of type [arg_type] to a term of type [abs_type], if
    the abstraction can be applied to the argument *)
and get_application_type (abs_type : recursive_type) (arg_type : recursive_type)
    : recursive_type option =
  (* Flatten the abstraction type to remove recursive type variables *)
  let abs_type_flat = flatten_union abs_type.union abs_type.context in
  (* The argument should be applicable to any function in the union, so acquire the type of applying the arg to each base type *)
  let return_types_opt =
    list_map_opt
      (fun abs_type_base ->
        get_application_type_base (abs_type_base, abs_type.context) arg_type)
      abs_type_flat
  in
  (* Join all of the return types into a single union type, add the context *)
  (* Return types that come back have context abs_type.context, since abstractions determine their return types *)
  Option.map
    (fun return_types ->
      build_recursive_type (List.flatten return_types) abs_type.context)
    return_types_opt

and get_application_type_base
    ((abs_type_base, abs_context) : flat_base_type * recursive_context)
    (arg_type : recursive_type) : union_type option =
  match abs_type_base with
  (* Label types, universal quantifications, and their variables cannot be applied *)
  | FLabel _ | FUnivTypeVar _ | FUnivQuantification _ -> None
  (* An application against a function type is well-typed if the abstraction accepts a supertype of the argument type.
     The return type is the union of all return types that the argument might match with *)
  | FIntersection branches ->
      let abs_arg_exhaustive =
        get_abs_args_exhaustive (branches, abs_context) arg_type
      in
      if not abs_arg_exhaustive then None
      else
        let return_types =
          extract_return_types (branches, abs_context) arg_type
        in
        Some return_types

(* Determines if the branches of an abstraction form a supertype of the argument type*)
and get_abs_args_exhaustive
    ((branches, branches_context) : unary_function list * recursive_context)
    (arg_type : recursive_type) =
  let composite_arg_type = extract_composite_args branches in
  is_subtype arg_type (build_recursive_type composite_arg_type branches_context)

and extract_return_types
    ((branches, branches_context) : unary_function list * recursive_context)
    (arg_type : recursive_type) =
  List.fold_left
    (fun acc (func_arg, func_return) ->
      let func_arg_type = build_recursive_type func_arg branches_context in
      if has_intersection arg_type func_arg_type then acc @ func_return else acc)
    [] branches

and abstraction_branches_disjoint (branches : (recursive_type * term) list) :
    bool =
  let arg_types = extract_first branches in
  let arg_pairs = self_pairs arg_types in
  let disjoint_args =
    not (List.exists (fun (arg1, arg2) -> has_intersection arg1 arg2) arg_pairs)
  in
  disjoint_args

and get_abstraction_type (var_type_env : var_type_env)
    (branches : (recursive_type * term) list) =
  (* Determine the type for each branch *)
  let branch_types_opt = list_map_opt (get_branch_type var_type_env) branches in

  (* Unify the branch types into a single type for the entire abstraction *)
  Option.map unify_branch_types branch_types_opt

(* Determines the type for a single branch of an abstraction, in terms of the
    union types for the argument and return value, and their shared recursive
    context *)
and get_branch_type (var_type_env : var_type_env)
    ((arg_type, body) : recursive_type * term) : recursive_type option =
  (* Recursively determine the type of the body of the branch, based on the type of the argument *)
  let body_type_env = arg_type :: var_type_env in
  let body_type_opt = get_type_rec body body_type_env in

  (* If the body type is defined, compute their unary function type *)
  Option.map
    (fun body_type ->
      let (unified_arg_type, unified_body_type), context =
        get_unified_type_context_pair arg_type body_type
      in
      build_recursive_type
        [ Intersection [ (unified_arg_type, unified_body_type) ] ]
        context)
    body_type_opt

and unify_branch_types (branch_types : recursive_type list) =
  let unified_branch_types, context = get_unified_type_context branch_types in
  let func_types =
    List.fold_left
      (fun acc_funcs unary_func ->
        match unary_func with
        | [ Intersection [ (arg_type, body_type) ] ] ->
            (arg_type, body_type) :: acc_funcs
        | _ ->
            raise
              (Failure "Error destructuring branch type: was not expected shape"))
      [] unified_branch_types
  in
  let union_type = [ Intersection func_types ] in
  build_recursive_type union_type context

and get_univ_application_type (quantifier : recursive_type)
    (type_arg : recursive_type) : recursive_type option =
  (* Flatten the func type to get rid of recursive types *)
  let quantifier_flat = flatten_union quantifier.union quantifier.context in
  (* The type argument is applicable to any universal quantification in the union, so determine the types resulting
     from applying the type argument to each universal quantification in the union *)
  let return_types_opt =
    list_map_opt
      (fun quant_option ->
        get_univ_application_option_type
          (quant_option, quantifier.context)
          type_arg)
      quantifier_flat
  in
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
