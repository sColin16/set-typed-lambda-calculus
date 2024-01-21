open Structured.Metatypes
open Structured.TermTypes
open Structured.TypeOperations.Create
open TypeOperations.Union
open StructuredHelpers
open StructuredBool

let name = get_typed_term_unsafe (Const "Name")
let val_lambda = get_typed_term_unsafe (Const "Val")
let zero_label = get_typed_term_unsafe (Const "Zero")
let succ = get_typed_term_unsafe (Const "Succ")
let pred = get_typed_term_unsafe (Const "Pred")
let zero = get_typed_term_unsafe (Abstraction [ (name.stype, zero_label.term) ])

let rec generate_typed_num (num : int) =
  let term = if num >= 0 then generate_pos_num num else generate_neg_num num in
  get_typed_term_unsafe term

and generate_pos_num (num : int) = generate_pos_num_rec num zero.term
and generate_neg_num (num : int) = generate_neg_num_rec num zero.term

and generate_pos_num_rec (num : int) (base_term : term) =
  if num <= 0 then base_term
  else
    generate_pos_num_rec (num - 1)
      (Abstraction [ (name.stype, succ.term); (val_lambda.stype, base_term) ])

and generate_neg_num_rec (num : int) (base_term : term) =
  if num >= 0 then base_term
  else
    generate_neg_num_rec (num + 1)
      (Abstraction [ (name.stype, pred.term); (val_lambda.stype, base_term) ])

let single_rec_step (name_type : structured_type) (val_type : union_type) =
  base_to_structured_type
    (Intersection
       [
         (name.stype.union, name_type.union); (val_lambda.stype.union, val_type);
       ])

let rec generate_rec_step (name_type : structured_type) (val_type : union_type)
    (num : int) =
  generate_rec_step_rec name_type val_type num

and generate_rec_step_rec (name_type : structured_type) (base_type : union_type)
    (num : int) =
  if num = 0 then union_to_structured_type base_type
  else
    generate_rec_step_rec name_type (single_rec_step name_type base_type).union
      (num - 1)

let generate_succ_rec_step (num : int) =
  generate_rec_step succ.stype [ RecTypeVar 0 ] num

let generate_pred_rec_step (num : int) =
  generate_rec_step pred.stype [ RecTypeVar 0 ] num

let one = generate_typed_num 1
let two = generate_typed_num 2
let neg_one = generate_typed_num (-1)
let neg_two = generate_typed_num (-2)

let coi_positive_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         ( Coinductive,
           get_flat_union_type [ one.stype; generate_succ_rec_step 1 ] );
       ])

let ind_positive_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         (Inductive, get_flat_union_type [ one.stype; generate_succ_rec_step 1 ]);
       ])

let coi_negative_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         ( Coinductive,
           get_flat_union_type [ neg_one.stype; generate_pred_rec_step 1 ] );
       ])

let ind_negative_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         ( Inductive,
           get_flat_union_type [ neg_one.stype; generate_pred_rec_step 1 ] );
       ])

let coi_natural_number = get_type_union [ zero.stype; coi_positive_number ]
let coi_non_negative_number = get_type_union [ zero.stype; coi_negative_number ]

let coi_integer =
  get_type_union [ coi_negative_number; zero.stype; coi_positive_number ]

let ind_natural_number = get_type_union [ zero.stype; ind_positive_number ]
let ind_non_negative_number = get_type_union [ zero.stype; ind_negative_number ]

let ind_integer =
  get_type_union [ ind_negative_number; zero.stype; ind_positive_number ]

(* Integer types that include positive and negative infinity *)
let ind_integer_plus =
  get_type_union [ ind_negative_number; zero.stype; coi_positive_number ]

let ind_integer_minus =
  get_type_union [ coi_negative_number; zero.stype; ind_positive_number ]

let coi_pos_even_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         ( Coinductive,
           get_flat_union_type [ two.stype; generate_succ_rec_step 2 ] );
       ])

let ind_pos_even_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         (Inductive, get_flat_union_type [ two.stype; generate_succ_rec_step 2 ]);
       ])

let coi_neg_even_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         ( Coinductive,
           get_flat_union_type [ neg_two.stype; generate_pred_rec_step 2 ] );
       ])

let ind_neg_even_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         ( Inductive,
           get_flat_union_type [ neg_two.stype; generate_pred_rec_step 2 ] );
       ])

let coi_pos_odd_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         ( Coinductive,
           get_flat_union_type [ one.stype; generate_succ_rec_step 2 ] );
       ])

let ind_pos_odd_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         (Inductive, get_flat_union_type [ one.stype; generate_succ_rec_step 2 ]);
       ])

let coi_neg_odd_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         ( Coinductive,
           get_flat_union_type [ neg_one.stype; generate_pred_rec_step 2 ] );
       ])

let ind_neg_odd_number =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [
         ( Inductive,
           get_flat_union_type [ neg_one.stype; generate_pred_rec_step 2 ] );
       ])

let coi_even_integer =
  get_type_union [ coi_neg_even_number; zero.stype; coi_pos_even_number ]

let coi_odd_integer = get_type_union [ coi_neg_odd_number; coi_pos_odd_number ]

let ind_even_integer =
  get_type_union [ ind_neg_even_number; zero.stype; ind_pos_even_number ]

let ind_odd_integer = get_type_union [ ind_neg_odd_number; ind_pos_odd_number ]

let pos_infinity =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [ (Coinductive, get_flat_union_type [ generate_succ_rec_step 1 ]) ])

let neg_infinity =
  build_structured_type [ RecTypeVar 0 ]
    (build_recursive_context
       [ (Coinductive, get_flat_union_type [ generate_pred_rec_step 1 ]) ])

let infinity = get_type_union [ pos_infinity; neg_infinity ]

let unary_numerical_op =
  build_structured_type
    [ Intersection [ (ind_integer.union, ind_integer.union) ] ]
    ind_integer.context

let binary_numerical_op =
  build_structured_type
    [
      Intersection
        [
          ( ind_integer.union,
            [ Intersection [ (ind_integer.union, ind_integer.union) ] ] );
        ];
    ]
    ind_integer.context

let num_to_bool_op =
  build_structured_type
    [ Intersection [ (ind_integer.union, bool_type.union) ] ]
    ind_integer.context

let binary_num_to_bool_op =
  build_structured_type
    [
      Intersection
        [
          ( ind_integer.union,
            [ Intersection [ (ind_integer.union, bool_type.union) ] ] );
        ];
    ]
    ind_integer.context

(* Increments an inductive number by one *)
let increment =
  get_typed_term_unsafe
    (Abstraction
       [
         (ind_negative_number, Application (Variable 0, val_lambda.term));
         ( get_type_union [ zero.stype; ind_positive_number ],
           Abstraction
             [ (name.stype, succ.term); (val_lambda.stype, Variable 1) ] );
       ])

(* Decrements an inductive number by one *)
let decrement =
  get_typed_term_unsafe
    (Abstraction
       [
         ( get_type_union [ zero.stype; ind_negative_number ],
           Abstraction
             [ (name.stype, pred.term); (val_lambda.stype, Variable 1) ] );
         (ind_positive_number, Application (Variable 0, val_lambda.term));
       ])

(* Determines if a value is even or odd, leveraging the subtyping system *)
let is_even =
  get_typed_term_unsafe
    (Abstraction
       [
         (ind_even_integer, true_lambda.term);
         (ind_odd_integer, false_lambda.term);
       ])

let fix_binary_num_to_bool = fix ind_integer num_to_bool_op
let fix_binary_num_op = fix ind_integer unary_numerical_op

let is_equal =
  get_typed_term_unsafe
    (fix_binary_num_to_bool
       (Abstraction
          [
            ( binary_num_to_bool_op,
              Abstraction
                [
                  ( zero.stype,
                    Abstraction
                      [
                        ( get_type_union
                            [ ind_positive_number; ind_negative_number ],
                          false_lambda.term );
                        (zero.stype, true_lambda.term);
                      ] );
                  ( ind_positive_number,
                    Abstraction
                      [
                        ( get_type_union [ zero.stype; ind_negative_number ],
                          false_lambda.term );
                        ( ind_positive_number,
                          Application
                            ( Application
                                ( Variable 2,
                                  Application (decrement.term, Variable 1) ),
                              Application (decrement.term, Variable 0) ) );
                      ] );
                  ( ind_negative_number,
                    Abstraction
                      [
                        ( get_type_union [ zero.stype; ind_positive_number ],
                          false_lambda.term );
                        ( ind_negative_number,
                          Application
                            ( Application
                                ( Variable 2,
                                  Application (increment.term, Variable 1) ),
                              Application (increment.term, Variable 0) ) );
                      ] );
                ] );
          ]))

let add =
  get_typed_term_unsafe
    (fix_binary_num_op
       (Abstraction
          [
            ( binary_numerical_op,
              Abstraction
                [
                  (zero.stype, Abstraction [ (ind_integer, Variable 0) ]);
                  ( ind_negative_number,
                    Abstraction
                      [
                        ( ind_integer,
                          Application
                            ( Application
                                ( Variable 2,
                                  Application (increment.term, Variable 1) ),
                              Application (decrement.term, Variable 0) ) );
                      ] );
                  ( ind_positive_number,
                    Abstraction
                      [
                        ( ind_integer,
                          Application
                            ( Application
                                ( Variable 2,
                                  Application (decrement.term, Variable 1) ),
                              Application (increment.term, Variable 0) ) );
                      ] );
                ] );
          ]))

(* Later, consider also implementing these functions *)
(* subtract *)
(* fibonnaci *)
(* negate *)
(* multiply *)
(* divide *)
