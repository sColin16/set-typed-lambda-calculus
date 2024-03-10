open TypeOperations.Subtype
open TypeOperations.Intersection
open SetTypedLambdaExample.Boolean
open SetTypedLambdaExample.Unions
open SetTypedLambdaExample.ExampleHelpers
open TypeOperations.Union
open TestHelpers

let () =
  test "Exhaustive function coverage of union A"
    (is_subtype split_unary_bool
       (type_union
          [
            split_identity_type;
            split_not_type;
            split_unary_true_type;
            split_unary_false_type;
          ]))

let () =
  test "Exhaustive function coverage of union B"
    (is_subtype
       (type_union
          [
            split_identity_type;
            split_not_type;
            split_unary_true_type;
            split_unary_false_type;
          ])
       split_unary_bool)

let () =
  test "Incomplete function coverage of union A"
    (not
       (is_subtype split_unary_bool
          (type_union
             [ split_identity_type; split_not_type; split_unary_false_type ])))

let () =
  test "Incomplete function coverage of union B"
    (is_subtype
       (type_union
          [ split_identity_type; split_not_type; split_unary_false_type ])
       split_unary_bool)

let () =
  test "Incomplete function coverage of union C"
    (not
       (is_subtype split_unary_bool
          (type_union
             [
               split_identity_type;
               split_unary_false_type;
               split_unary_true_type;
             ])))

let () =
  test "Incomplete function coverage of union D"
    (is_subtype
       (type_union
          [ split_identity_type; split_unary_false_type; split_unary_true_type ])
       split_unary_bool)

let () =
  test "Non-unary function splitting A"
    (not
       (is_subtype unary_bool_op
          (type_union [ unary_true_type; unary_false_type ])))

let () =
  test "Non-unary function splitting B"
    (is_subtype
       (type_union [ unary_true_type; unary_false_type ])
       unary_bool_op)

let () =
  test "Exhaustive function coverage with extras A"
    (is_subtype
       (type_union [ split_unary_bool; and_lambda.rtype ])
       (type_union
          [
            split_identity_type;
            split_not_type;
            split_unary_true_type;
            split_unary_false_type;
            binary_bool_op;
          ]))

let () =
  test "Exhaustive function coverage with extras B"
    (is_subtype
       (type_union
          [
            and_lambda.rtype;
            split_identity_type;
            split_not_type;
            split_unary_true_type;
            split_unary_false_type;
          ])
       (type_union [ split_unary_bool; binary_bool_op ]))

let () =
  test "Increment three bit has expected type A"
    (is_subtype increment_three_bit.rtype increment_three_bit_type_expected)

let () =
  test "Increment three bit has expected type B"
    (is_subtype increment_three_bit_type_expected increment_three_bit.rtype)

let () =
  test "Decrement three bit has expected type A"
    (is_subtype decrement_three_bit.rtype decrement_three_bit_type_expected)

let () =
  test "Decrement three bit has expected type B"
    (is_subtype decrement_three_bit_type_expected decrement_three_bit.rtype)

let () =
  test "Increment three bit is a unary number operation"
    (is_subtype increment_three_bit.rtype unary_num_type)

let () =
  test "Decrement three bit is a unary number operation"
    (is_subtype decrement_three_bit.rtype unary_num_type)

let () =
  test "Add is a binary number operation"
    (is_subtype add_three_bit.rtype binary_num_type)

let () =
  test "Increment zero"
    (evaluates_to
       (Application (increment_three_bit.term, zero.term))
       one.term)

let () =
  test "zero plus one"
    (evaluates_to
       (binary_apply add_three_bit.term one.term zero.term)
       one.term)

let () =
  test "one plus one"
    (evaluates_to
       (binary_apply add_three_bit.term one.term one.term)
       two.term)

let () =
  test "two plus two"
    (evaluates_to
       (binary_apply add_three_bit.term two.term two.term)
       four.term)

let () =
  test "three plus seven"
    (evaluates_to
       (binary_apply add_three_bit.term three.term seven.term)
       two.term)

let () = test "zero and zero" (has_intersection zero.rtype zero.rtype)
let () = test "zero and one" (not (has_intersection zero.rtype one.rtype))
let () = test "one and two" (not (has_intersection one.rtype two.rtype))
let () = test "zero and two" (not (has_intersection zero.rtype two.rtype))
let () = test "different functions A" (not (is_subtype one.rtype two.rtype))
let () = test "different functions B" (not (is_subtype two.rtype one.rtype))
