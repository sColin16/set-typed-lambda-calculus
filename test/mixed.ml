open TypeOperations.Subtype
open TypeOperations.Union
open SetTypedLambdaExample.ModularArithmetic
open SetTypedLambdaExample.Boolean
open SetTypedLambdaExample.Mixed
open SetTypedLambdaExample.ExampleHelpers
open TestHelpers
open TypeOperations.Create

let is_even_odd_type_expected =
  func_type
    ( (type_union [ is_even_label.rtype; is_odd_label.rtype ]).union,
      num_to_bool.union )

let () =
  test "is_zero is num to bool type" (is_subtype is_zero.rtype num_to_bool)

let () =
  test "is_even_odd has expected mutually recursive type"
    (is_subtype is_even_odd.rtype is_even_odd_type_expected)

let () =
  test "is_even is num to bool type" (is_subtype is_even.rtype num_to_bool)

let () = test "is_odd is num to bool type" (is_subtype is_odd.rtype num_to_bool)

let () =
  test "zero is zero"
    (evaluates_to (Application (is_zero.term, zero.term)) true_lambda.term)

let () =
  test "two is not zero"
    (evaluates_to (Application (is_zero.term, two.term)) false_lambda.term)

let () =
  test "zero is even"
    (evaluates_to (Application (is_even.term, zero.term)) true_lambda.term)

let () =
  test "one is odd"
    (evaluates_to (Application (is_odd.term, one.term)) true_lambda.term)

let () =
  test "six is even"
    (evaluates_to (Application (is_even.term, six.term)) true_lambda.term)

let () =
  test "seven is odd"
    (evaluates_to (Application (is_odd.term, seven.term)) true_lambda.term)

let () =
  test "zero is not odd"
    (evaluates_to (Application (is_odd.term, zero.term)) false_lambda.term)

let () =
  test "one is not even"
    (evaluates_to (Application (is_even.term, one.term)) false_lambda.term)

let () =
  test "six is not odd"
    (evaluates_to (Application (is_odd.term, six.term)) false_lambda.term)

let () =
  test "seven is not even"
    (evaluates_to (Application (is_even.term, seven.term)) false_lambda.term)
