open Metatypes
open Create

let rec shift_rec_type_vars_union (amount : int) (union : union_type) =
  List.map (shift_rec_type_vars_base amount) union

(* TODO: is there a way to avoid basically repeating this for the flat types? *)
and shift_rec_type_vars_base (amount : int) (base_type : base_type) =
  match base_type with
  | Label _ | UnivTypeVar _ -> base_type
  | RecTypeVar n -> RecTypeVar (n + amount)
  | Intersection functions ->
      Intersection (List.map (shift_rec_type_vars_func amount) functions)
  | UnivQuantification t ->
      UnivQuantification (shift_rec_type_vars_union amount t)

and shift_rec_type_vars_func (amount : int) ((arg, return) : unary_function) =
  (shift_rec_type_vars_union amount arg, shift_rec_type_vars_union amount return)

and shift_rec_type_vars_context (amount : int) (context : recursive_context) =
  List.map (shift_rec_type_vars_def amount) context

and shift_rec_type_vars_def (amount : int) (recursive_def : recursive_def) =
  let shifted_union =
    List.map
      (fun flat_base ->
        match flat_base with
        | FLabel _ | FUnivTypeVar _ -> flat_base
        | FIntersection functions ->
            FIntersection (List.map (shift_rec_type_vars_func amount) functions)
        | FUnivQuantification t ->
            FUnivQuantification (shift_rec_type_vars_union amount t))
      recursive_def.flat_union
  in
  build_recursive_def recursive_def.kind shifted_union

let get_type_in_context (t : structured_type)
    (recursive_context : recursive_context) : structured_type =
  let shift_amount = List.length recursive_context in
  let new_context = shift_rec_type_vars_context shift_amount t.context in
  let new_union =
    shift_rec_type_vars_union (List.length recursive_context) t.union
  in
  build_structured_type new_union (recursive_context @ new_context)

(* Converts a pair of structured types into a pair of union types that share a context *)
let get_unified_type_context_pair (typea: structured_type) (typeb: structured_type) =
  let recontextualized_typeb = get_type_in_context typeb typea.context in
  let new_typeb = recontextualized_typeb.union in
  ((typea.union, new_typeb), recontextualized_typeb.context)

(* Converts a list of structured types into a list of union types and a common context they all share,
   shifting recursive type variables in the union as appropriate *)
let get_unified_type_context (types : structured_type list) =
  let new_unions_rev, new_context =
    List.fold_left
      (fun (acc_union, acc_context) next_type ->
        let recontextualized_next_union = get_type_in_context next_type acc_context in
        let new_acc_union = recontextualized_next_union.union :: acc_union in
        let new_acc_context = recontextualized_next_union.context in
        (new_acc_union, new_acc_context))
      ([], []) types in
  (* We must reverse the list of unions since we fold left but want to keep the types in the right order *)
  let new_unions = List.rev new_unions_rev in
  new_unions, new_context

(* TODO: consider writing more dedicated logic for this rather than the showving intermediate into intersection *)
(* Takes a list of arg types and their corresponding body types, and joined them into
   a single structured type for the intersection of the functions *)
let unify_function_types (arg_types: structured_type list) (body_types: structured_type list) =
  (* First, build individual unary function types for each arg/body pair *)
  let unary_types = List.map2 (fun arg_type body_type ->
    let (new_arg_type, new_body_type), new_context = get_unified_type_context_pair arg_type body_type in
    build_structured_type [ Intersection [(new_arg_type, new_body_type )]] new_context
  ) arg_types body_types in
  (* Then, rectonextualize all of them so we can prepare to join them into a single type *)
  let new_unary_unions, new_context = get_unified_type_context unary_types in
  (* Then destructure all of the unary types to build a single intersection type *)
  let unary_list = List.fold_left (fun acc_func_types next_union ->
    match next_union with
    | [ Intersection [ next_unary ]] -> next_unary::acc_func_types
    | _ -> raise (Failure "there was a problem destructuring the unary function types")
  ) [] new_unary_unions in
  build_structured_type [ Intersection unary_list ] new_context