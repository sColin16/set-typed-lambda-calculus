open Metatypes
open TypeOperations.Subtype
open TypeOperations.Intersection
open TypeOperations.Unary
open TypeOperations.Union
open TypeOperations.WellFounded
open SetTypedLambdaExample.Recursive
open SetTypedLambdaExample.Boolean
open SetTypedLambdaExample.ExampleHelpers
open TermOperations.Eval
open TermOperations.ValToTerm
open TermTypes

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let is_equivalent_type (t1 : recursive_type) (t2 : recursive_type) =
  is_subtype t1 t2 && is_subtype t2 t1

let is_strict_subtype (t1 : recursive_type) (t2 : recursive_type) =
  is_subtype t1 t2 && not (is_subtype t2 t1)

let evaluates_to term value = value_to_term (eval term) = value

(* Generate a term to check if two numbers are equal, in the lambda calculus *)
let numeric_terms_equal_term num1 num2 =
  binary_apply is_equal.term (typed_term_num num1).term
    (typed_term_num num2).term

let numeric_terms_equal num1 num2 =
  evaluates_to (numeric_terms_equal_term num1 num2) true_lambda.term

let numeric_terms_not_equal num1 num2 =
  evaluates_to (numeric_terms_equal_term num1 num2) false_lambda.term

let numeric_terms_add_term num1 num2 =
  binary_apply add.term (typed_term_num num1).term (typed_term_num num2).term

let assert_adds_to num1 num2 num3 =
  evaluates_to (numeric_terms_add_term num1 num2) (typed_term_num num3).term

let () =
  test "Coninductive even or odd integers equal to coinductive integer"
    (is_equivalent_type coi_integer
       (type_union [ coi_even_integer; coi_odd_integer ]))

let () =
  test "Inductive even or odd integers equal to inductive integer"
    (is_equivalent_type ind_integer
       (type_union [ ind_even_integer; ind_odd_integer ]))

let () =
  test "Inductive integer or pos/neg infinity equal to coinductive integer"
    (is_equivalent_type coi_integer (type_union [ ind_integer; infinity ]))

let () =
  test
    "Inductive integers with positive infinity strict subtype of coinductive \
     integers"
    (is_strict_subtype ind_integer_plus coi_integer)

let () =
  test
    "Inductive integers with negative infinity strict subtype of coinductive \
     integers"
    (is_strict_subtype ind_integer_minus coi_integer)

(* These coinductive types have an inhabited intersection, the infinite function type *)
let () =
  test "Coinductive even and odd integers have an intersection"
    (has_intersection coi_even_integer coi_odd_integer)

(* But the inductive versions intentionally do not have an intersection *)
let () =
  test "Inductive even and odd integers don't have an intersection"
    (not (has_intersection ind_even_integer ind_odd_integer))

let () =
  test "Pos/neg infinity is subtype of coinductive integers"
    (is_subtype infinity coi_integer)

let () =
  test "Pos/neg infinity is subtype of coinductive even integers"
    (is_subtype infinity coi_even_integer)

let () =
  test "Pos/neg infinity is subtype of coinductive odd integers"
    (is_subtype infinity coi_odd_integer)

let () =
  test "Pos/neg infinity is not a subtype of inductive integers"
    (not (is_subtype infinity ind_integer))

let () =
  test "Pos/neg infinity is not a subtype of inductive even integers"
    (not (is_subtype infinity ind_even_integer))

let () =
  test "Pos/neg infinity is not a subtype of inductive odd integers"
    (not (is_subtype infinity ind_odd_integer))

let () =
  test
    "Pos infinity is a subtype of inductive integers with inductive positives"
    (is_subtype pos_infinity ind_integer_plus)

let () =
  test
    "Neg infinity is not a subtype of inductive integers with inductive \
     positives"
    (not (is_subtype neg_infinity ind_integer_plus))

let () =
  test
    "Pos infinity is not a subtype of inductive integers with inductive \
     negatives"
    (not (is_subtype pos_infinity ind_integer_minus))

let () =
  test
    "Neg infinity is a subtype of inductive integers with inductive negatives"
    (is_subtype neg_infinity ind_integer_minus)

let () =
  test "Zero is a subtype of coinductive integers"
    (is_subtype zero.rtype coi_integer)

let () =
  test "Zero is a subtype of conindutive even integers"
    (is_subtype zero.rtype coi_even_integer)

let () =
  test "Zero is a not subtype of coninductive odd integers"
    (not (is_subtype zero.rtype coi_odd_integer))

let () =
  test "One is a subtype of coinductive integers"
    (is_subtype one.rtype coi_integer)

let () =
  test "One is not a subtype of coinductive even integers"
    (not (is_subtype one.rtype coi_even_integer))

let () =
  test "One is a subtype of coninductive odd integers"
    (is_subtype one.rtype coi_odd_integer)

let () =
  test "Negative two is a subtype of coinductive integers"
    (is_subtype neg_two.rtype coi_integer)

let () =
  test "Negative two is a subtype of coinductive even integers"
    (is_subtype neg_two.rtype coi_even_integer)

let () =
  test "Negative two is not a subtype of coninductive odd integers"
    (not (is_subtype neg_two.rtype coi_odd_integer))

let () =
  test "inductive integers are a strict subtype of coninductive integers"
    (is_strict_subtype ind_integer coi_integer)

let () =
  test "coinductive and inductive integers have an intersction"
    (has_intersection ind_integer coi_integer)

let () =
  test "inductive integers do not intersect with infinity"
    (not (has_intersection ind_integer infinity))

let () = test "positive infinity is a unary type" (is_unary pos_infinity)
let () = test "negative infinity is a unary type" (is_unary pos_infinity)

let () =
  test "inductive integers are well-founded"
    (is_well_founded_union ind_integer.union ind_integer.context)

let () =
  test "Pos/neg infinity is not well-founded"
    (not (is_well_founded_union infinity.union infinity.context))

let () =
  test "Increment is a unary number operation"
    (is_subtype increment.rtype unary_numerical_op)

let () =
  test "Decrement is a unary number operation"
    (is_subtype decrement.rtype unary_numerical_op)

(* TODO: consider checking the more specific types of these functions *)

let () =
  test "Three increments to four"
    (evaluates_to
       (Application (increment.term, (typed_term_num 3).term))
       (typed_term_num 4).term)

let () =
  test "Negative two increment to negative one"
    (evaluates_to
       (Application (increment.term, (typed_term_num (-2)).term))
       (typed_term_num (-1)).term)

let () =
  test "Three decrements to two"
    (evaluates_to
       (Application (decrement.term, (typed_term_num 3).term))
       (typed_term_num 2).term)

let () =
  test "Negative one decrements to negative two"
    (evaluates_to
       (Application (decrement.term, (typed_term_num (-1)).term))
       (typed_term_num (-2)).term)

let () =
  test "is_even is a number to bool operation"
    (is_subtype is_even.rtype num_to_bool_op)

let () =
  test "four is even"
    (evaluates_to
       (Application (is_even.term, (typed_term_num 4).term))
       true_lambda.term)

let () =
  test "five is not even"
    (evaluates_to
       (Application (is_even.term, (typed_term_num 5).term))
       false_lambda.term)

let () =
  test "is_equal is of type num -> num -> bool"
    (is_subtype is_equal.rtype binary_num_to_bool_op)

let () = test "2 equals 2" (numeric_terms_equal 2 2)
let () = test "-4 equals -4" (numeric_terms_equal (-4) (-4))
let () = test "3 is not equal to 1" (numeric_terms_not_equal 3 1)
let () = test "-2 is not equal to -3" (numeric_terms_not_equal (-2) (-3))
let () = test "-1 is not equal to 4" (numeric_terms_not_equal (-1) 4)
let () = test "2 is not equal to -3" (numeric_terms_not_equal 2 (-3))

let () =
  test "add is a binary numerical operation"
    (is_subtype add.rtype binary_numerical_op)

let () = test "3 plus 5 is 8" (assert_adds_to 3 5 8)
let () = test "-2 plus -4 is -6" (assert_adds_to (-2) (-4) (-6))
let () = test "-4 plus 2 is -2" (assert_adds_to (-4) 2 (-2))
let () = test "5 plus -2 is 3" (assert_adds_to 5 (-2) 3)
