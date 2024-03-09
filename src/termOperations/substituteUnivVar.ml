open Metatypes
open TermTypes
open Common.Helpers
open ShiftUnivVar
open TypeOperations.ShiftUnivVar
open TypeOperations.SubstituteUnivVar

(* Substitutes the [with_type] into the [in_term] for universal type variables referencing
   the universal quantification at this level (0, or higher if nested within another universal quantifications) *)
let rec substitute_univ_var_term (with_type : recursive_type) (in_term : term) :
    term =
  (* Shift the universal type indices in the argument by one since it is about to be substituted into a universal quantification,
     where their binding quantification is one further away *)
  let shifted_with_type = shift_univ_var_type with_type 1 in
  (* Perform the substitution on universal quantification variables that are bound to this universal quantification *)
  let substitution_result =
    substitute_univ_var_term_rec 0 shifted_with_type in_term
  in
  (* Finally shift everything down one since we remove a universal quantification where
     the binding quantification is one closer *)
  let final_result = shift_univ_var_term substitution_result (-1) in
  final_result

and substitute_univ_var_term_rec (variable_num : int)
    (with_type : recursive_type) (in_term : term) : term =
  match in_term with
  (* Variables and constants have nothing to substitute *)
  | Variable _ | Const _ -> in_term
  (* Applications are substituted recursively *)
  | Application (left_term, right_term) ->
      let left_subst, right_subst =
        map_pair
          (substitute_univ_var_term_rec variable_num with_type)
          (left_term, right_term)
      in
      Application (left_subst, right_subst)
  (* Abstractions are recursive, but we substitute in the term and types separately *)
  | Abstraction branches ->
      let substituted_branches =
        List.map
          (fun (branch_type, branch_body) ->
            ( substitute_univ_var_type_rec variable_num with_type branch_type,
              substitute_univ_var_term_rec variable_num with_type branch_body ))
          branches
      in
      Abstraction substituted_branches
  (* Universal application is also substituted recursively for the term and type *)
  | UnivApplication (inner_term, inner_type) ->
      UnivApplication
        ( substitute_univ_var_term_rec variable_num with_type inner_term,
          substitute_univ_var_type_rec variable_num with_type inner_type )
  (* Universal quantifiers require special logic to honor the de Bruijn indices *)
  | UnivQuantifier inner_term ->
      (* We increment the variable we substitute for by one since we are descending through another quantifier *)
      let new_var_num = variable_num + 1 in
      (* We shift the variables in the with type by one since the type is about to be placed one quantifier deeper,
         and so the bounding quantifiers for the variables will be one further away *)
      let new_with_type = shift_univ_var_type with_type 1 in
      (* Perform the recursive substitution *)
      let substituted_inner_term =
        substitute_univ_var_term_rec new_var_num new_with_type inner_term
      in
      (* And wrap the substituted result in a quantifier again *)
      UnivQuantifier substituted_inner_term
