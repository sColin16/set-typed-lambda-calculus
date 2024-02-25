open LambdaCalculus.Structured.TypeOperations.Subtype
open LambdaCalculus.Structured.TypeOperations.Union
open LambdaCalculus.StructuredArithmetic
open LambdaCalculus.StructuredBool
open LambdaCalculus.StructuredMixed
open LambdaCalculus.StructuredHelpers
open LambdaCalculus.TestHelpers
open TypeOperations.Create

let is_even_odd_type_expected =
  func_type
    ( (type_union [ is_even_label.stype; is_odd_label.stype ]).union,
      num_to_bool.union )

let () =
  test "is_zero is num to bool type" (is_subtype is_zero.stype num_to_bool)

let () =
  test "is_even_odd has expected mutually recursive type"
    (is_subtype is_even_odd.stype is_even_odd_type_expected)

let () =
  test "is_even is num to bool type" (is_subtype is_even.stype num_to_bool)

let () = test "is_odd is num to bool type" (is_subtype is_odd.stype num_to_bool)

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
