open ExampleHelpers
open TypeOperations.Union
open TypeOperations.Create
open TermOperations.Helpers

let zero = typed_term (Const "Zero")
let one = typed_term (Const "One")
let two = typed_term (Const "Two")
let three = typed_term (Const "Three")
let four = typed_term (Const "Four")
let five = typed_term (Const "Five")
let six = typed_term (Const "Six")
let seven = typed_term (Const "Seven")

let three_bit_type =
  type_union
    [
      zero.rtype;
      one.rtype;
      two.rtype;
      three.rtype;
      four.rtype;
      five.rtype;
      six.rtype;
      seven.rtype;
    ]

let unary_num_op = func_type (three_bit_type.union, three_bit_type.union)
let binary_num_op = func_type (three_bit_type.union, unary_num_op.union)

let increment =
  typed_term
    (Abstraction
       [
         (zero.rtype, one.term);
         (one.rtype, two.term);
         (two.rtype, three.term);
         (three.rtype, four.term);
         (four.rtype, five.term);
         (five.rtype, six.term);
         (six.rtype, seven.term);
         (seven.rtype, zero.term);
       ])

let decrement =
  typed_term
    (Abstraction
       [
         (zero.rtype, seven.term);
         (one.rtype, zero.term);
         (two.rtype, one.term);
         (three.rtype, two.term);
         (four.rtype, three.term);
         (five.rtype, four.term);
         (six.rtype, five.term);
         (seven.rtype, six.term);
       ])

let fix_binary_num_op = fix three_bit_type unary_num_op
let fix_unary_num_op = fix three_bit_type three_bit_type

let add =
  typed_term
    (fix_binary_num_op
       (Abstraction
          [
            ( binary_num_op,
              Abstraction
                [
                  (zero.rtype, Abstraction [ (three_bit_type, Variable 0) ]);
                  ( type_union
                      [
                        one.rtype;
                        two.rtype;
                        three.rtype;
                        four.rtype;
                        five.rtype;
                        six.rtype;
                        seven.rtype;
                      ],
                    Abstraction
                      [
                        ( three_bit_type,
                          binary_apply (Variable 2)
                            (Application (decrement.term, Variable 1))
                            (Application (increment.term, Variable 0)) );
                      ] );
                ] );
          ]))

let fib =
  typed_term
    (fix_unary_num_op
       (Abstraction
          [
            ( unary_num_op,
              Abstraction
                [
                  (type_union [ zero.rtype; one.rtype ], one.term);
                  ( type_union
                      [
                        two.rtype;
                        three.rtype;
                        four.rtype;
                        five.rtype;
                        six.rtype;
                        seven.rtype;
                      ],
                    binary_apply add.term
                      (Application
                         (Variable 1, Application (decrement.term, Variable 0)))
                      (Application
                         ( Variable 1,
                           Application
                             ( decrement.term,
                               Application (decrement.term, Variable 0) ) )) );
                ] );
          ]))
