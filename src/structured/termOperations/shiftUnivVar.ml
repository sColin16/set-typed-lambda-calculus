open TermTypes
open Common.Helpers
open TypeOperations.ShiftUnivVar

(** Shift free universal type variables in a term by the shift amount *)
let rec shift_univ_var_term (term : term) (shift_amount : int) =
  shift_univ_var_term_rec shift_amount 0 term

and shift_univ_var_term_rec (shift_amount : int) (cutoff : int) (term : term) =
  match term with
  (* Variables and consts don't need anything shifted *)
  | Variable _ | Const _ -> term
  (* Applications are shifted recursively *)
  | Application (left_term, right_term) ->
      let left_shifted, right_shifted =
        map_pair
          (shift_univ_var_term_rec shift_amount cutoff)
          (left_term, right_term)
      in
      Application (left_shifted, right_shifted)
  (* Abstractions are substituted recursively as well *)
  | Abstraction branches ->
      let shifted_branches =
        List.map
          (fun (branch_type, branch_body) ->
            ( shift_univ_var_type_rec shift_amount cutoff branch_type,
              shift_univ_var_term_rec shift_amount cutoff branch_body ))
          branches
      in
      Abstraction shifted_branches
  (* Universal applications are substituted recursively *)
  | UnivApplication (inner_term, inner_type) ->
      let term_shifted =
        shift_univ_var_term_rec shift_amount cutoff inner_term
      in
      let type_shifted =
        shift_univ_var_type_rec shift_amount cutoff inner_type
      in
      UnivApplication (term_shifted, type_shifted)
  (* Universal quantifiers increment the cutoff by one since the index of free variables increases by one when passing through a quantifier *)
  | UnivQuantifier inner_term ->
      UnivQuantifier
        (shift_univ_var_term_rec shift_amount (cutoff + 1) inner_term)
