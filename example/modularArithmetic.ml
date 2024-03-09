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
      zero.stype;
      one.stype;
      two.stype;
      three.stype;
      four.stype;
      five.stype;
      six.stype;
      seven.stype;
    ]

let unary_num_op = func_type (three_bit_type.union, three_bit_type.union)
let binary_num_op = func_type (three_bit_type.union, unary_num_op.union)

let increment =
  typed_term
    (Abstraction
       [
         (zero.stype, one.term);
         (one.stype, two.term);
         (two.stype, three.term);
         (three.stype, four.term);
         (four.stype, five.term);
         (five.stype, six.term);
         (six.stype, seven.term);
         (seven.stype, zero.term);
       ])

let decrement =
  typed_term
    (Abstraction
       [
         (zero.stype, seven.term);
         (one.stype, zero.term);
         (two.stype, one.term);
         (three.stype, two.term);
         (four.stype, three.term);
         (five.stype, four.term);
         (six.stype, five.term);
         (seven.stype, six.term);
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
                  (zero.stype, Abstraction [ (three_bit_type, Variable 0) ]);
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
                  (type_union [ zero.stype; one.stype ], one.term);
                  ( type_union
                      [
                        two.stype;
                        three.stype;
                        four.stype;
                        five.stype;
                        six.stype;
                        seven.stype;
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
