open ExampleHelpers
open ModularArithmetic
open Boolean
open TypeOperations.Union
open TypeOperations.Create
open TermOperations.Helpers

let is_even_label = typed_term (Const "isEven")
let is_odd_label = typed_term (Const "isOdd")
let is_even_odd_label = type_union [ is_even_label.stype; is_odd_label.stype ]
let name = typed_term (Const "Name")
let num_to_bool = func_type (three_bit_type.union, bool_type.union)

let is_zero =
  typed_term
    (Abstraction
       [
         (zero.stype, true_lambda.term);
         ( type_union
             [
               one.stype;
               two.stype;
               three.stype;
               four.stype;
               five.stype;
               six.stype;
               seven.stype;
             ],
           false_lambda.term );
       ])

let fix_even_odd = fix is_even_odd_label num_to_bool

let is_even_odd =
  typed_term
    (fix_even_odd
       (Abstraction
          [
            ( func_type (is_even_odd_label.union, num_to_bool.union),
              Abstraction
                [
                  ( is_even_label.stype,
                    Abstraction
                      [
                        (zero.stype, true_lambda.term);
                        ( type_union
                            [
                              one.stype;
                              two.stype;
                              three.stype;
                              four.stype;
                              five.stype;
                              six.stype;
                              seven.stype;
                            ],
                          binary_apply (Variable 2) is_odd_label.term
                            (Application (decrement.term, Variable 0)) );
                      ] );
                  ( is_odd_label.stype,
                    Abstraction
                      [
                        (zero.stype, false_lambda.term);
                        ( type_union
                            [
                              one.stype;
                              two.stype;
                              three.stype;
                              four.stype;
                              five.stype;
                              six.stype;
                              seven.stype;
                            ],
                          binary_apply (Variable 2) is_even_label.term
                            (Application (decrement.term, Variable 0)) );
                      ] );
                ] );
          ]))

let is_even = typed_term (Application (is_even_odd.term, is_even_label.term))
let is_odd = typed_term (Application (is_even_odd.term, is_odd_label.term))
