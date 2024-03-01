open LambdaCalculus.StructuredPoly
open LambdaCalculus.StructuredBool
open LambdaCalculus.Structured.TypeOperations.Subtype
open LambdaCalculus.Structured.Metatypes
open LambdaCalculus.StructuredHelpers
open LambdaCalculus.StructuredRecursive
open TypeOperations.Create
open TypeOperations.Intersection
open TermTypes
open TypeOperations.Map
open LambdaCalculus.TestHelpers
open TermOperations.Helpers

let univ_quantify_union (union : union_type) = [ UnivQuantification union ]

let univ_quantify_union_double (union : union_type) =
  [ UnivQuantification [ UnivQuantification union ] ]

let identity_int =
  typed_term (UnivApplication (polymoprhic_identity.term, ind_integer))

let identity_bool =
  typed_term (UnivApplication (polymoprhic_identity.term, bool_type))

let double_int =
  typed_term (UnivApplication (polymorphic_double.term, ind_integer))

let quadruple_int =
  typed_term (UnivApplication (polymorphic_quadruple.term, ind_integer))

let expected_poly_identity_type =
  base_type
    (UnivQuantification
       [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ])

let expected_applied_poly_type =
  map_type (fun integer -> [ Intersection [ (integer, integer) ] ]) ind_integer

let expected_poly_map_type =
  base_type
    (UnivQuantification
       [
         Intersection
           [
             ( [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ],
               [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ] );
           ];
       ])

let expected_poly_map_applied_type =
  map_type
    (fun int ->
      [
        Intersection
          [ ([ Intersection [ (int, int) ] ], [ Intersection [ (int, int) ] ]) ];
      ])
    ind_integer

(* Represents `forall X. X -> List X -> List X`, when final return can be asserted to be non-empty *)
let expected_cons_supertype =
  map_type
    (fun polymoprhic_list_union ->
      [
        UnivQuantification
          [
            Intersection
              [
                ( [ UnivTypeVar 0 ],
                  [
                    Intersection
                      [ (polymoprhic_list_union, polymoprhic_list_union) ];
                  ] );
              ];
          ];
      ])
    polymoprhic_list_type.full

(* Represents `forall X. X -> List X -> NonEmptyList X` which is the most specific type *)
let expected_cons_type =
  map_type2
    (fun list non_empty ->
      [
        UnivQuantification
          [
            Intersection
              [ ([ UnivTypeVar 0 ], [ Intersection [ (list, non_empty) ] ]) ];
          ];
      ])
    polymoprhic_list_type.full polymoprhic_list_type.non_empty

(* Represents `forall X. (NonEmptyList X -> false) & (EmptyList -> true)`, the most specific type *)
let expected_is_empty_type =
  map_type
    (fun non_empty ->
      [
        UnivQuantification
          [
            Intersection
              [
                (non_empty, false_lambda.stype.union);
                (empty_list.stype.union, true_lambda.stype.union);
              ];
          ];
      ])
    polymoprhic_list_type.non_empty

(* Represents `forall X. List X -> Bool` a more general type for the function *)
let expected_is_empty_supertype =
  map_type
    (fun list ->
      [ UnivQuantification [ Intersection [ (list, bool_type.union) ] ] ])
    polymoprhic_list_type.full

(* Represents `forall X. (NonEmptyList X -> X) & (EmptyList -> None)`, the most specific type *)
let expected_head_type =
  map_type
    (fun non_empty ->
      [
        UnivQuantification
          [
            Intersection
              [
                (non_empty, [ UnivTypeVar 0 ]);
                (empty_list.stype.union, none_label.stype.union);
              ];
          ];
      ])
    polymoprhic_list_type.non_empty

(* Represents `forall X. (List X -> X | None)` a more general type *)
let expected_head_supertype =
  map_type
    (fun list ->
      [
        UnivQuantification
          [ Intersection [ (list, UnivTypeVar 0 :: none_label.stype.union) ] ];
      ])
    polymoprhic_list_type.full

(* Represents `forall X. (NonEmptyList X -> List X) & (EmptyList -> None)`, the most specific type *)
let expected_tail_type =
  map_type2
    (fun list non_empty ->
      [
        UnivQuantification
          [
            Intersection
              [
                (non_empty, list);
                (empty_list.stype.union, none_label.stype.union);
              ];
          ];
      ])
    polymoprhic_list_type.full polymoprhic_list_type.non_empty

(* Represents `forall X. (List X -> (List X) | None), the more general type *)
let expected_tail_supertype =
  map_type
    (fun list ->
      [
        UnivQuantification
          [ Intersection [ (list, none_label.stype.union @ list) ] ];
      ])
    polymoprhic_list_type.full

(* TODO: assert that this functions returns a non-empty list with types *)
let expected_append_type =
  map_type
    (fun list ->
      [
        UnivQuantification
          [
            Intersection
              [ (list, [ Intersection [ ([ UnivTypeVar 0 ], list) ] ]) ];
          ];
      ])
    polymoprhic_list_type.full

let simple_boolean_list = build_bool_list_term [ true; false ]
let simple_integer_list = build_int_list_term [ -1; 1; 2; -2 ]
let integer_list_b = build_int_list_term [ 0; -1 ]
let integer_list_combined = build_int_list_term [ -1; 1; 2; -2; 0; -1 ]
let incrementing_integer_list = build_int_list_term [ 1; 2; 3; 4 ]
let is_empty_bool = typed_term (UnivApplication (is_empty.term, bool_type))
let head_bool = typed_term (UnivApplication (head.term, bool_type))
let tail_bool = typed_term (UnivApplication (tail.term, bool_type))
let length_bool = typed_term (UnivApplication (length.term, bool_type))
let length_int = typed_term (UnivApplication (length.term, ind_integer))
let nth_bool = typed_term (UnivApplication (nth.term, bool_type))
let nth_int = typed_term (UnivApplication (nth.term, ind_integer))
let concat_int = typed_term (UnivApplication (concat.term, ind_integer))
let append_int = typed_term (UnivApplication (append.term, ind_integer))
let reverse_int = typed_term (UnivApplication (reverse.term, ind_integer))
let filter_bool = typed_term (UnivApplication (filter.term, bool_type))
let filter_int = typed_term (UnivApplication (filter.term, ind_integer))

let map_int_bool =
  typed_term
    (UnivApplication (UnivApplication (map.term, ind_integer), bool_type))

let fold_int_int =
  typed_term
    (UnivApplication (UnivApplication (fold_left.term, ind_integer), ind_integer))

let every_int = typed_term (UnivApplication (every.term, ind_integer))

let true_predicate =
  typed_term
    (UnivQuantifier
       (Abstraction [ (base_type (UnivTypeVar 0), true_lambda.term) ]))

let false_predicate =
  typed_term
    (UnivQuantifier
       (Abstraction [ (base_type (UnivTypeVar 0), false_lambda.term) ]))

let true_predicate_int =
  typed_term (UnivApplication (true_predicate.term, ind_integer))

let false_predicate_int =
  typed_term (UnivApplication (false_predicate.term, ind_integer))

(* Represents `forall X. (X -> Bool) -> X List -> Bool`, the type for every and exists *)
let list_predicate_type =
  map_type
    (fun list ->
      [
        UnivQuantification
          [
            Intersection
              [
                ( [ Intersection [ ([ UnivTypeVar 0 ], bool_type.union) ] ],
                  [ Intersection [ (list, bool_type.union) ] ] );
              ];
          ];
      ])
    polymoprhic_list_type.full

let () =
  test "Polymoprhic identity function type"
    (is_equivalent_type polymoprhic_identity.stype expected_poly_identity_type)

let () =
  test "Polymoprhic identity function applied type"
    (is_equivalent_type identity_int.stype expected_applied_poly_type)

let () =
  test "Polymoprhic double function type"
    (is_equivalent_type polymorphic_double.stype expected_poly_map_type)

let () =
  test "Polymoprhic double function applied type"
    (is_equivalent_type double_int.stype expected_poly_map_applied_type)

let () =
  test "Polymorphic quadruple function type"
    (is_equivalent_type polymorphic_quadruple.stype expected_poly_map_type)

let () =
  test "Polymoprhic quadruple function applied type"
    (is_equivalent_type quadruple_int.stype expected_poly_map_applied_type)

let () =
  test "Simple polymoprhic evaluation"
    (evaluates_to (Application (identity_int.term, zero.term)) zero.term)

let () =
  test "Double polymorphic eval with increment"
    (evaluates_to
       (binary_apply double_int.term increment.term two.term)
       (num_term 4))

let () =
  test "Double polymorphic eval with decrement"
    (evaluates_to
       (binary_apply double_int.term decrement.term zero.term)
       (num_term (-2)))

let () =
  test "Quadruple polymorphic with increment"
    (evaluates_to
       (binary_apply quadruple_int.term increment.term (num_term 6))
       (num_term 10))

let () =
  test "Quadruple polymorphic with decrement"
    (evaluates_to
       (binary_apply quadruple_int.term decrement.term (num_term 5))
       one.term)

let () =
  test "Boolean non-empty list is subtype of boolean list"
    (is_subtype boolean_list_type.non_empty boolean_list_type.full)

let () =
  test "empty list is a subtype of boolean list"
    (is_subtype empty_list.stype boolean_list_type.full)

let () =
  test "empty list is not a subtype of non empty boolean list"
    (not (is_subtype empty_list.stype boolean_list_type.non_empty))

let () =
  test "empty list and boolean non-empty list do not have an intersection"
    (not (has_intersection empty_list.stype boolean_list_type.non_empty))

let () =
  test "Polymoprhic non-empty list is a subtype of polymoprhic list"
    (is_subtype polymoprhic_list_type.non_empty polymoprhic_list_type.full)

let () =
  test "Polymoprhic cons is a subtype of more general type"
    (is_strict_subtype cons.stype expected_cons_supertype)

let () =
  test "Polymoprhic cons has expected specific type"
    (is_equivalent_type cons.stype expected_cons_type)

let () =
  test "Polymoprhic is_empty has expected specific type"
    (is_equivalent_type is_empty.stype expected_is_empty_type)

let () =
  test "Polymoprhic is_empty is a subtype of more general type"
    (is_strict_subtype is_empty.stype expected_is_empty_supertype)

let () =
  test "Polymoprhic is_empty detects empty list correctly"
    (evaluates_to
       (Application (is_empty_bool.term, empty_list.term))
       true_lambda.term)

let () =
  test "Polymorphic is_empty detects non-empty list correctly"
    (evaluates_to
       (Application (is_empty_bool.term, simple_boolean_list.term))
       false_lambda.term)

let () =
  test "Polymoprhic head has expected specific type"
    (is_equivalent_type head.stype expected_head_type)

let () =
  test "Polymorphic head has expected more general type"
    (is_strict_subtype head.stype expected_head_supertype)

let () =
  test "Polymoprhic tail has expected specific type"
    (is_equivalent_type tail.stype expected_tail_type)

let () =
  test "Polymorphic tail has expected more general type"
    (is_strict_subtype tail.stype expected_tail_supertype)

let apply_head_non_empty =
  typed_term (Application (head_bool.term, simple_boolean_list.term))

let apply_head_empty =
  typed_term (Application (head_bool.term, empty_list.term))

let () =
  test "Polymorphic head pulls first element for non-empty list"
    (evaluates_to apply_head_non_empty.term true_lambda.term)

let () =
  test "Polymoprhic head on non-empty list types correctly"
    (is_equivalent_type apply_head_non_empty.stype bool_type)

let () =
  test "Polymorphic head returns None for empty list"
    (evaluates_to apply_head_empty.term none_label.term)

let () =
  test "Polymorphic head types correctly applied on empty list"
    (is_equivalent_type apply_head_empty.stype none_label.stype)

let () =
  test "Polymorphic tail gets rest of list for non-empty list"
    (evaluates_to
       (Application (tail_bool.term, simple_boolean_list.term))
       (build_bool_list_term [ false ]).term)

let () =
  test "Polymoprhic tail returns None for empty list"
    (evaluates_to
       (Application (tail_bool.term, empty_list.term))
       none_label.term)

let () =
  test "Length is a list to num operation"
    (is_subtype length.stype (map_type univ_quantify_union list_to_num_op))

let () =
  test "Empty integer list has length 0"
    (evaluates_to (Application (length_int.term, empty_list.term)) zero.term)

let () =
  test "Empty boolean list has length 0"
    (evaluates_to (Application (length_bool.term, empty_list.term)) zero.term)

let () =
  test "Simple boolean list has correct length"
    (evaluates_to
       (Application (length_bool.term, simple_boolean_list.term))
       two.term)

let () =
  test "Simple integer list has correct length"
    (evaluates_to
       (Application (length_int.term, simple_integer_list.term))
       (num_term 4))

let () =
  test "nth is a list index operation"
    (is_subtype nth.stype (map_type univ_quantify_union list_idx_op))

let () =
  test "first in empty list is none"
    (evaluates_to
       (binary_apply nth_int.term empty_list.term zero.term)
       none_label.term)

let () =
  test "third in empty list is none"
    (evaluates_to
       (binary_apply nth_int.term empty_list.term (num_term 3))
       none_label.term)

let () =
  test "second is simple boolean list is correct"
    (evaluates_to
       (binary_apply nth_bool.term simple_boolean_list.term one.term)
       false_lambda.term)

let () =
  test "third in simple integer list is correct"
    (evaluates_to
       (binary_apply nth_int.term simple_integer_list.term two.term)
       two.term)

let () =
  test "out of bound in integer list is none"
    (evaluates_to
       (binary_apply nth_int.term simple_integer_list.term (num_term 7))
       none_label.term)

let () =
  test "Concat is a binary list operation"
    (is_subtype concat.stype (map_type univ_quantify_union binary_list_op))

let () =
  test "Concat two empty lists is empty list"
    (evaluates_to
       (binary_apply concat_int.term empty_list.term empty_list.term)
       empty_list.term)

let () =
  test "Concat empty list with integer list is integer list"
    (evaluates_to
       (binary_apply concat_int.term simple_integer_list.term empty_list.term)
       simple_integer_list.term)

let () =
  test "Concat integer list with empty list is integer list"
    (evaluates_to
       (binary_apply concat_int.term empty_list.term simple_integer_list.term)
       simple_integer_list.term)

let () =
  test "Concat two non-empty integer lists is correct"
    (evaluates_to
       (binary_apply concat_int.term simple_integer_list.term
          integer_list_b.term)
       integer_list_combined.term)

let () =
  test "Append has expected type" (is_subtype append.stype expected_append_type)

let () =
  test "Append to empty list is list with just that element"
    (evaluates_to
       (binary_apply append_int.term empty_list.term neg_one.term)
       (build_int_list_term [ -1 ]).term)

let () =
  test "Append to non-empty list is correct"
    (evaluates_to
       (binary_apply append_int.term integer_list_b.term two.term)
       (build_int_list_term [ 0; -1; 2 ]).term)

let () =
  test "Reverse is a unary list type"
    (is_subtype reverse.stype (map_type univ_quantify_union unary_list_op))

let () =
  test "Reverse of empty list is empty list"
    (evaluates_to
       (Application (reverse_int.term, empty_list.term))
       empty_list.term)

let () =
  test "Reverse of integer list is correct"
    (evaluates_to
       (Application (reverse_int.term, simple_integer_list.term))
       (build_list_term [ neg_two.term; two.term; one.term; neg_one.term ]).term)

let () =
  test "Filter has the appropriate type"
    (is_subtype filter.stype (map_type univ_quantify_union filter_op))

let () =
  test "Filter boolean list with identity"
    (evaluates_to
       (binary_apply filter_bool.term simple_boolean_list.term
          identity_bool.term)
       (build_bool_list_term [ true ]).term)

let () =
  test "Filter numeric list for evens"
    (evaluates_to
       (binary_apply filter_int.term simple_integer_list.term is_even.term)
       (build_int_list_term [ 2; -2 ]).term)

let () =
  test "Filter numeric list for odds"
    (evaluates_to
       (binary_apply filter_int.term simple_integer_list.term is_odd.term)
       (build_int_list_term [ -1; 1 ]).term)

let () =
  test "Filter empty list yields empty list"
    (evaluates_to
       (binary_apply filter_int.term empty_list.term is_even.term)
       empty_list.term)

let () =
  test "Filter with always true predicate retains list"
    (evaluates_to
       (binary_apply filter_int.term simple_integer_list.term
          true_predicate_int.term)
       simple_integer_list.term)

let () =
  test "Filter with always false predicate clears list"
    (evaluates_to
       (binary_apply filter_int.term simple_integer_list.term
          false_predicate_int.term)
       empty_list.term)

let () =
  test "Map has the appropriate type"
    (is_subtype map.stype (map_type univ_quantify_union_double map_op))

let () =
  test "Map empty list is an empty list"
    (evaluates_to
       (binary_apply map_int_bool.term is_even.term empty_list.term)
       empty_list.term)

let () =
  test "Map for is_even over integer list is correct"
    (evaluates_to
       (binary_apply map_int_bool.term is_even.term simple_integer_list.term)
       (build_bool_list_term [ false; false; true; true ]).term)

let () =
  test "Map for is_odd over integer list is correct"
    (evaluates_to
       (binary_apply map_int_bool.term is_odd.term simple_integer_list.term)
       (build_bool_list_term [ true; true; false; false ]).term)

let () =
  test "Map always returning false is correct"
    (evaluates_to
       (binary_apply map_int_bool.term false_predicate_int.term
          simple_integer_list.term)
       (build_bool_list_term [ false; false; false; false ]).term)

let () =
  test "Fold left has appropriate type"
    (is_subtype fold_left.stype (map_type univ_quantify_union_double fold_op))

let () =
  test "Fold left uses accumulator for empty list"
    (evaluates_to
       (trinary_apply fold_int_int.term add.term two.term empty_list.term)
       two.term)

let () =
  test "Fold left sums integer list"
    (evaluates_to
       (trinary_apply fold_int_int.term add.term zero.term
          incrementing_integer_list.term)
       (num_term 10))

let () =
  test "Every function has the right type"
    (is_subtype every.stype list_predicate_type)

let () =
  test "Every function called on empty list returns true"
    (evaluates_to
       (binary_apply every_int.term is_even.term empty_list.term)
       true_lambda.term)

let () =
  test "Every is_even on simple list is false"
    (evaluates_to
       (binary_apply every_int.term is_even.term simple_integer_list.term)
       false_lambda.term)

let () =
  test "Every is_positive on incrementing integer list is true"
    (evaluates_to
       (binary_apply every_int.term
          (Abstraction
             [
               (ind_positive_number, true_lambda.term);
               (ind_non_positive_number, false_lambda.term);
             ])
          incrementing_integer_list.term)
       true_lambda.term)
