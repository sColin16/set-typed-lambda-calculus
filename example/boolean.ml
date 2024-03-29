open TypeOperations.Union
open TypeOperations.Create
open ExampleHelpers

let true_lambda = typed_term (Const "True")
let false_lambda = typed_term (Const "False")
let bool_type = type_union [ true_lambda.rtype; false_lambda.rtype ]
let unary_bool_op = func_type (bool_type.union, bool_type.union)
let binary_bool_op = func_type (bool_type.union, unary_bool_op.union)
let ternary_bool_op = func_type (bool_type.union, binary_bool_op.union)
let identity_lambda = typed_term (Abstraction [ (bool_type, Variable 0) ])

let not_lambda =
  typed_term
    (Abstraction
       [
         (true_lambda.rtype, false_lambda.term);
         (false_lambda.rtype, true_lambda.term);
       ])

let and_lambda =
  typed_term
    (Abstraction
       [
         (true_lambda.rtype, identity_lambda.term);
         (false_lambda.rtype, Abstraction [ (bool_type, false_lambda.term) ]);
       ])

let or_lambda =
  typed_term
    (Abstraction
       [
         (true_lambda.rtype, Abstraction [ (bool_type, true_lambda.term) ]);
         (false_lambda.rtype, identity_lambda.term);
       ])

let if_lambda =
  typed_term
    (Abstraction
       [
         ( true_lambda.rtype,
           Abstraction [ (bool_type, Abstraction [ (bool_type, Variable 1) ]) ]
         );
         ( false_lambda.rtype,
           Abstraction [ (bool_type, Abstraction [ (bool_type, Variable 0) ]) ]
         );
       ])
