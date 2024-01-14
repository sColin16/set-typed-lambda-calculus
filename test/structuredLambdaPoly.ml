open LambdaCalculus.StructuredPoly
open LambdaCalculus.StructuredBool
open LambdaCalculus.Structured.TermOperations.Eval
open LambdaCalculus.Structured.TermOperations.ValToTerm
open LambdaCalculus.Structured.TypeOperations.Subtype
open LambdaCalculus.Structured.Metatypes
open LambdaCalculus.StructuredHelpers
open LambdaCalculus.StructuredArithmetic
open TypeOperations.Create
open TypeOperations.Context
open TypeOperations.Intersection

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let evaluates_to term value = value_to_term (eval term) = value

let is_equivalent_type (t1 : structured_type) (t2 : structured_type) =
  is_subtype t1 t2 && is_subtype t2 t1

let is_strict_subtype (t1 : structured_type) (t2 : structured_type) =
  is_subtype t1 t2 && not (is_subtype t2 t1)

let applied_poly_identity =
  get_typed_term_unsafe
    (UnivApplication (polymoprhic_identity.term, name_label.stype))

let applied_poly_double =
  get_typed_term_unsafe
    (UnivApplication (polymorphic_double.term, three_bit_type))

let applied_poly_quadruple =
  get_typed_term_unsafe
    (UnivApplication (polymorphic_quadruple.term, three_bit_type))

let expected_poly_identity_type =
  base_to_structured_type
    (UnivQuantification
       [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ])

let expected_applied_poly_type =
  base_to_structured_type
    (Intersection [ (name_label.stype.union, name_label.stype.union) ])

let expected_poly_map_type =
  base_to_structured_type
    (UnivQuantification
       [
         Intersection
           [
             ( [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ],
               [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ] );
           ];
       ])

let expected_poly_map_applied_type =
  base_to_structured_type
    (Intersection
       [
         ( [ Intersection [ (three_bit_type.union, three_bit_type.union) ] ],
           [ Intersection [ (three_bit_type.union, three_bit_type.union) ] ] );
       ])

(* Represents `forall X. X -> List X -> List X`, when final return can be asserted to be non-empty *)
let expected_cons_supertype =
  build_structured_type
    [
      UnivQuantification
        [
          Intersection
            [
              ( [ UnivTypeVar 0 ],
                [
                  Intersection
                    [
                      ( polymoprhic_list_type.full.union,
                        polymoprhic_list_type.full.union );
                    ];
                ] );
            ];
        ];
    ]
    polymoprhic_list_type.full.context

(* Recontextualize this type so we can use both types in the type below *)
(* TODO: investigate replacing this with a call to get_unified_type_context_pair *)
let recontexted_non_empty =
  get_type_in_context polymoprhic_list_type.non_empty
    polymoprhic_list_type.full.context

(* Represents `forall X. X -> List X -> NonEmptyList X` which is the most specific type *)
let expected_cons_type =
  build_structured_type
    [
      UnivQuantification
        [
          Intersection
            [
              ( [ UnivTypeVar 0 ],
                [
                  Intersection
                    [
                      ( polymoprhic_list_type.full.union,
                        recontexted_non_empty.union );
                    ];
                ] );
            ];
        ]
      (* Use the combined context for this type *);
    ]
    recontexted_non_empty.context

(* Represents `forall X. (NonEmptyList X -> false) & (EmptyList -> true)`, the most specific type *)
let expected_is_empty_type =
  build_structured_type
    [
      UnivQuantification
        [
          Intersection
            [
              (polymoprhic_list_type.non_empty.union, false_lambda.stype.union);
              (empty_list.stype.union, true_lambda.stype.union);
            ];
        ];
    ]
    polymoprhic_list_type.non_empty.context

(* Represents `forall X. List X -> Bool` a more general type for the function *)
let expected_is_empty_supertype =
  build_structured_type
    [
      UnivQuantification
        [ Intersection [ (polymoprhic_list_type.full.union, bool_type.union) ] ];
    ]
    polymoprhic_list_type.full.context

(* Represents `forall X. (NonEmptyList X -> X) & (EmptyList -> None)`, the most specific type *)
let expected_head_type =
  build_structured_type
    [
      UnivQuantification
        [
          Intersection
            [
              (polymoprhic_list_type.non_empty.union, [ UnivTypeVar 0 ]);
              (empty_list.stype.union, none_label.stype.union);
            ];
        ];
    ]
    polymoprhic_list_type.non_empty.context

(* Represents `forall X. (List X -> X | None)` a more general type *)
let expected_head_supertype =
  build_structured_type
    [
      UnivQuantification
        [
          Intersection
            [
              ( polymoprhic_list_type.full.union,
                UnivTypeVar 0 :: none_label.stype.union );
            ];
        ];
    ]
    polymoprhic_list_type.full.context

(* Represents `forall X. (NonEmptyList X -> List X) & (EmptyList -> None)`, the most specific type *)
let expected_tail_type =
  build_structured_type
    [
      UnivQuantification
        [
          Intersection
            [
              (recontexted_non_empty.union, polymoprhic_list_type.full.union);
              (empty_list.stype.union, none_label.stype.union);
            ];
        ];
    ]
    recontexted_non_empty.context

(* Represents `forall X. (List X -> (List X) | None), the more general type *)
let expected_tail_supertype =
  build_structured_type
    [
      UnivQuantification
        [
          Intersection
            [
              ( polymoprhic_list_type.full.union,
                none_label.stype.union @ polymoprhic_list_type.full.union );
            ];
        ];
    ]
    polymoprhic_list_type.full.context

let simple_boolean_list =
  build_list_term [ true_lambda.term; false_lambda.term ]

let () =
  test "Polymoprhic identity function type"
    (is_equivalent_type polymoprhic_identity.stype expected_poly_identity_type)

let () =
  test "Polymoprhic identity function applied type"
    (is_equivalent_type applied_poly_identity.stype expected_applied_poly_type)

let () =
  test "Polymoprhic double function type"
    (is_equivalent_type polymorphic_double.stype expected_poly_map_type)

let () =
  test "Polymoprhic double function applied type"
    (is_equivalent_type applied_poly_double.stype expected_poly_map_applied_type)

let () =
  test "Polymorphic quadruple function type"
    (is_equivalent_type polymorphic_quadruple.stype expected_poly_map_type)

let () =
  test "Polymoprhic quadruple function applied type"
    (is_equivalent_type applied_poly_quadruple.stype
       expected_poly_map_applied_type)

let () =
  test "Simple polymoprhic evaluation"
    (evaluates_to
       (Application (applied_poly_identity.term, name_label.term))
       name_label.term)

let () =
  test "Double polymorphic eval with increment"
    (evaluates_to
       (Application
          (Application (applied_poly_double.term, increment.term), two.term))
       four.term)

let () =
  test "Double polymorphic eval with decrement"
    (evaluates_to
       (Application
          (Application (applied_poly_double.term, decrement.term), zero.term))
       six.term)

let () =
  test "Quadruple polymorphic with increment"
    (evaluates_to
       (Application
          (Application (applied_poly_quadruple.term, increment.term), six.term))
       two.term)

let () =
  test "Quadruple polymorphic with decrement"
    (evaluates_to
       (Application
          (Application (applied_poly_quadruple.term, decrement.term), five.term))
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
       (Application (UnivApplication (is_empty.term, bool_type), empty_list.term))
       true_lambda.term)

let () =
  test "Polymorphic is_empty detects non-empty list correctly"
    (evaluates_to
       (Application
          (UnivApplication (is_empty.term, bool_type), simple_boolean_list.term))
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
  get_typed_term_unsafe
    (Application
       (UnivApplication (head.term, bool_type), simple_boolean_list.term))

let apply_head_empty =
  get_typed_term_unsafe
    (Application (UnivApplication (head.term, bool_type), empty_list.term))

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
       (Application
          (UnivApplication (tail.term, bool_type), simple_boolean_list.term))
       (build_list_term [ false_lambda.term ]).term)

let () =
  test "Polymoprhic tail returns None for empty list"
    (evaluates_to
       (Application (UnivApplication (tail.term, bool_type), empty_list.term))
       none_label.term)
