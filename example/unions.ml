open TermTypes
open ExampleHelpers
open Boolean
open TypeOperations.Union
open TypeOperations.Create
open TermOperations.Helpers

let split_unary_bool =
  base_type
    (Intersection
       [
         (true_lambda.rtype.union, bool_type.union);
         (false_lambda.rtype.union, bool_type.union);
       ])

let split_identity_type =
  base_type
    (Intersection
       [
         (true_lambda.rtype.union, true_lambda.rtype.union);
         (false_lambda.rtype.union, false_lambda.rtype.union);
       ])

let split_not_type =
  base_type
    (Intersection
       [
         (true_lambda.rtype.union, false_lambda.rtype.union);
         (false_lambda.rtype.union, true_lambda.rtype.union);
       ])

let split_unary_true_type =
  base_type
    (Intersection
       [
         (true_lambda.rtype.union, true_lambda.rtype.union);
         (false_lambda.rtype.union, true_lambda.rtype.union);
       ])

let split_unary_false_type =
  base_type
    (Intersection
       [
         (true_lambda.rtype.union, false_lambda.rtype.union);
         (false_lambda.rtype.union, false_lambda.rtype.union);
       ])

let unary_true_type = func_type (bool_type.union, true_lambda.rtype.union)
let unary_false_type = func_type (bool_type.union, false_lambda.rtype.union)
let name = typed_term (Const "Name")
let val_lambda = typed_term (Const "Val")
let zero_label = typed_term (Const "Zero")
let succ = typed_term (Const "Succ")

let increment_term term =
  Abstraction [ (name.rtype, succ.term); (val_lambda.rtype, term) ]

let zero = typed_term (Abstraction [ (name.rtype, zero_label.term) ])
let one = typed_term (increment_term zero.term)
let two = typed_term (increment_term one.term)
let three = typed_term (increment_term two.term)
let four = typed_term (increment_term three.term)
let five = typed_term (increment_term four.term)
let six = typed_term (increment_term five.term)
let seven = typed_term (increment_term six.term)

let three_bit_num =
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

let unary_num_type = func_type (three_bit_num.union, three_bit_num.union)
let binary_num_type = func_type (three_bit_num.union, unary_num_type.union)

let increment_three_bit =
  typed_term
    (Abstraction
       [
         ( type_union
             [
               zero.rtype;
               one.rtype;
               two.rtype;
               three.rtype;
               four.rtype;
               five.rtype;
               six.rtype;
             ],
           Abstraction
             [ (name.rtype, Const "Succ"); (val_lambda.rtype, Variable 1) ] );
         (seven.rtype, zero.term);
       ])

let decrement_three_bit =
  typed_term
    (Abstraction
       [
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
           Application (Variable 0, val_lambda.term) );
         (zero.rtype, seven.term);
       ])

let fix_binary_num_op = fix three_bit_num unary_num_type

let add_three_bit =
  typed_term
    (fix_binary_num_op
       (Abstraction
          [
            ( binary_num_type,
              Abstraction
                [
                  (zero.rtype, Abstraction [ (three_bit_num, Variable 0) ]);
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
                        ( three_bit_num,
                          binary_apply (Variable 2)
                            (Application (decrement_three_bit.term, Variable 1))
                            (Application (increment_three_bit.term, Variable 0))
                        );
                      ] );
                ] );
          ]))

let increment_three_bit_type_expected =
  base_type
    (Intersection
       [
         ( (type_union
              [
                zero.rtype;
                one.rtype;
                two.rtype;
                three.rtype;
                four.rtype;
                five.rtype;
                six.rtype;
              ])
             .union,
           (type_union
              [
                one.rtype;
                two.rtype;
                three.rtype;
                four.rtype;
                five.rtype;
                six.rtype;
                seven.rtype;
              ])
             .union );
         (seven.rtype.union, zero.rtype.union);
       ])

let decrement_three_bit_type_expected =
  base_type
    (Intersection
       [
         ( (type_union
              [
                one.rtype;
                two.rtype;
                three.rtype;
                four.rtype;
                five.rtype;
                six.rtype;
                seven.rtype;
              ])
             .union,
           (type_union
              [
                zero.rtype;
                one.rtype;
                two.rtype;
                three.rtype;
                four.rtype;
                five.rtype;
                six.rtype;
              ])
             .union );
         (zero.rtype.union, seven.rtype.union);
       ])
