open LambdaCalculus.Structured.TypeOperations.Subtype
open LambdaCalculus.StructuredBool
open LambdaCalculus.TestHelpers
open TermOperations.Helpers

let () =
  test "identity is unary bool op"
    (is_subtype identity_lambda.stype unary_bool_op)

let () = test "not is unary bool op" (is_subtype not_lambda.stype unary_bool_op)

let () =
  test "and is binary bool op" (is_subtype and_lambda.stype binary_bool_op)

let () = test "or is binary bool op" (is_subtype or_lambda.stype binary_bool_op)

let () =
  test "if is ternary bool op" (is_subtype if_lambda.stype ternary_bool_op)

let () =
  test "not true"
    (evaluates_to
       (Application (not_lambda.term, true_lambda.term))
       false_lambda.term)

let () =
  test "not false"
    (evaluates_to
       (Application (not_lambda.term, false_lambda.term))
       true_lambda.term)

let () =
  test "true and true"
    (evaluates_to
       (binary_apply and_lambda.term true_lambda.term true_lambda.term)
       true_lambda.term)

let () =
  test "true and false"
    (evaluates_to
       (binary_apply and_lambda.term true_lambda.term false_lambda.term)
       false_lambda.term)

let () =
  test "false and true"
    (evaluates_to
       (binary_apply and_lambda.term false_lambda.term true_lambda.term)
       false_lambda.term)

let () =
  test "false and false"
    (evaluates_to
       (binary_apply and_lambda.term false_lambda.term false_lambda.term)
       false_lambda.term)

let () =
  test "true or true"
    (evaluates_to
       (binary_apply or_lambda.term true_lambda.term true_lambda.term)
       true_lambda.term)

let () =
  test "true or false"
    (evaluates_to
       (binary_apply or_lambda.term true_lambda.term false_lambda.term)
       true_lambda.term)

let () =
  test "false or true"
    (evaluates_to
       (binary_apply or_lambda.term false_lambda.term true_lambda.term)
       true_lambda.term)

let () =
  test "false or false"
    (evaluates_to
       (binary_apply or_lambda.term false_lambda.term false_lambda.term)
       false_lambda.term)
