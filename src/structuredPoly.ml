open Structured.Metatypes
open Structured.TermTypes
open Structured.TypeOperations.Create
open TypeOperations.Helpers
open TypeOperations.Context
open StructuredHelpers
open StructuredBool
open StructuredRecursive
open TermOperations.Helpers
open TypeOperations.Map

let name_label = typed_term (Const "Name")
let val_label = typed_term (Const "Val")
let next_label = typed_term (Const "Next")
let nil_label = typed_term (Const "Nil")
let cons_label = typed_term (Const "Cons")
let none_label = typed_term (Const "None")

let polymoprhic_identity =
  typed_term
    (UnivQuantifier (Abstraction [ (base_type (UnivTypeVar 0), Variable 0) ]))

let polymorphic_double =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            ( func_type ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]),
              Abstraction
                [
                  ( base_type (UnivTypeVar 0),
                    Application
                      (Variable 1, Application (Variable 1, Variable 0)) );
                ] );
          ]))

let polymorphic_double_poly =
  UnivApplication (polymorphic_double.term, base_type (UnivTypeVar 0))

let polymorphic_quadruple =
  typed_term
    (UnivQuantifier
       (Application
          ( UnivApplication
              ( polymorphic_double.term,
                func_type ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ),
            polymorphic_double_poly )))

let empty_list = typed_term (Abstraction [ (name_label.stype, nil_label.term) ])

type list_type_pair = { full : structured_type; non_empty : structured_type }

(** Constructs a list type for a list that holds the given type *)
let build_list_type (kind : recursive_kind) (elt_type : structured_type) =
  (* We are going to add a new recursive definition to the context, whose number is the length of the current context *)
  (* The alternative is getting the elt_type in a new context, but the elt_type is part of that context, so we need to
     add this recursive definition to the context instead *)
  let new_rec_num = List.length elt_type.context in
  let flat_empty_type =
    flatten_union empty_list.stype.union empty_list.stype.context
  in
  (* A node of a list contains the value and the rest of the list *)
  let flat_non_empty_type =
    FIntersection
      [
        (name_label.stype.union, cons_label.stype.union);
        (val_label.stype.union, elt_type.union);
        (next_label.stype.union, [ RecTypeVar new_rec_num ]);
      ]
  in
  let flat_list_type = flat_non_empty_type :: flat_empty_type in
  let list_recursive_def = build_recursive_def kind flat_list_type in
  (* Add the new recursive definition to the end of the context so it has the number assigned originally *)
  let new_context = elt_type.context @ [ list_recursive_def ] in
  build_structured_type [ RecTypeVar new_rec_num ] new_context

(** Constructs a non-empty list type type for a list that holds the given type *)
let build_non_empty_list_type (kind : recursive_kind)
    (elt_type : structured_type) =
  let list_type = build_list_type kind elt_type in
  (* Just assert that at least one node exists containing a value and pointing to a possible empty list *)
  (* TODO: avoid duplication with Flat and non-flat intersection *)
  build_structured_type
    [
      Intersection
        [
          (name_label.stype.union, cons_label.stype.union);
          (val_label.stype.union, elt_type.union);
          (next_label.stype.union, list_type.union);
        ];
    ]
    list_type.context

let build_list_type_pair (kind : recursive_kind) (elt_type : structured_type) =
  let list_type = build_list_type kind elt_type in
  let non_empty_list_type = build_non_empty_list_type kind elt_type in
  { full = list_type; non_empty = non_empty_list_type }

(* Converts a list of terms to a term in the lambda calculus representing that list *)
let rec build_list_term (term_list : term list) =
  typed_term (build_list_term_rec term_list)

and build_list_term_rec (term_list : term list) =
  match term_list with
  | [] -> empty_list.term
  | term :: rest ->
      let rest_list = build_list_term_rec rest in
      Abstraction
        [
          (name_label.stype, cons_label.term);
          (val_label.stype, term);
          (next_label.stype, rest_list);
        ]

let build_bool_list_term (bools : bool list) =
  let term_list =
    List.map
      (function true -> true_lambda.term | false -> false_lambda.term)
      bools
  in
  build_list_term term_list

let build_int_list_term (ints : int list) =
  let term_list = (List.map num_term) ints in
  build_list_term term_list

let build_nested_int_list_term (ints : int list list) =
  let term_list =
    (List.map (fun int_list ->
         build_list_term_rec ((List.map num_term) int_list)))
      ints
  in
  build_list_term term_list

let boolean_list_type = build_list_type_pair Inductive bool_type

let polymoprhic_list_type =
  build_list_type_pair Inductive (base_type (UnivTypeVar 0))

let polymorphic_list_type_nested1 =
  build_list_type_pair Inductive (base_type (UnivTypeVar 1))

let polymoprhic_nested_list_type =
  build_list_type_pair Inductive polymoprhic_list_type.full

let (list_with_num_union, num_with_list_union), list_num_context =
  get_unified_type_context_pair polymoprhic_list_type.full ind_integer

let list_to_num_op =
  build_structured_type
    [ Intersection [ (list_with_num_union, num_with_list_union) ] ]
    list_num_context

let (list_with_idx_union, idx_with_list_union), list_idx_context =
  get_unified_type_context_pair polymoprhic_list_type.full ind_natural_number

(* Represents `Nat -> X | None`, the "return value" of the list_idx_op function *)
let idx_to_elt_op =
  build_structured_type
    [
      Intersection
        [ (idx_with_list_union, UnivTypeVar 0 :: none_label.stype.union) ];
    ]
    list_idx_context

(* Represents `List X -> Nat -> X | None`, when embedded in some universal quantifier with binding variable X *)
let list_idx_op =
  build_structured_type
    [ Intersection [ (list_with_idx_union, idx_to_elt_op.union) ] ]
    list_idx_context

let unary_list_op =
  build_structured_type
    [
      Intersection
        [ (polymoprhic_list_type.full.union, polymoprhic_list_type.full.union) ];
    ]
    polymoprhic_list_type.full.context

let binary_list_op =
  build_structured_type
    [ Intersection [ (polymoprhic_list_type.full.union, unary_list_op.union) ] ]
    polymoprhic_list_type.full.context

(* Represents `X -> Bool`, the condition function for filtering polymoprhic lists *)
let poly_to_bool_op = func_type ([ UnivTypeVar 0 ], bool_type.union)

(* Represents `(X -> Bool) -> List X` *)
let cond_to_list_op =
  build_structured_type
    [
      Intersection [ (poly_to_bool_op.union, polymoprhic_list_type.full.union) ];
    ]
    polymoprhic_list_type.full.context

(* Represents `List X -> (X -> Bool) -> List X`, the signature for the polymoprhic list function *)
let filter_op =
  build_structured_type
    [
      Intersection [ (polymoprhic_list_type.full.union, cond_to_list_op.union) ];
    ]
    polymoprhic_list_type.full.context

(* Represents `List X -> List Y`, part of the polymorphic map type *)
let list_transform_op =
  map_type2
    (fun outer_list inner_list -> [ Intersection [ (outer_list, inner_list) ] ])
    polymorphic_list_type_nested1.full polymoprhic_list_type.full

(* Represents `(X -> Y) -> List X -> List Y, the signature for the polymoprhic map function *)
let map_op =
  map_type
    (fun list_transform_union ->
      [
        Intersection
          [
            ( [ Intersection [ ([ UnivTypeVar 1 ], [ UnivTypeVar 0 ]) ] ],
              list_transform_union );
          ];
      ])
    list_transform_op

(* Represents `Acc -> Elt -> Acc`, the function defining a step of a fold operation *)
let fold_step =
  func_type
    ( [ UnivTypeVar 0 ],
      [ Intersection [ ([ UnivTypeVar 1 ], [ UnivTypeVar 0 ]) ] ] )

(* Represents `Acc -> Elt List -> Acc`, part of the fold operation *)
let list_acc_op =
  map_type
    (fun list ->
      [
        Intersection
          [
            ([ UnivTypeVar 0 ], [ Intersection [ (list, [ UnivTypeVar 0 ]) ] ]);
          ];
      ])
    polymorphic_list_type_nested1.full

(* Represents `(Acc -> Elt -> Acc) -> Acc -> Elt List -> Acc`, the type for fold *)
let fold_op =
  map_type2
    (fun fold_step_union list_acc_union ->
      [ Intersection [ (fold_step_union, list_acc_union) ] ])
    fold_step list_acc_op

(* Represents `X -> X -> Bool`, the equality function provided to check list equality *)
let binary_poly_bool_op =
  func_type
    ( [ UnivTypeVar 0 ],
      [ Intersection [ ([ UnivTypeVar 0 ], bool_type.union) ] ] )

(* Represents `X List -> X List -> Bool`, the second half of the list quality function *)
let binary_list_bool_op =
  map_type
    (fun list ->
      [ Intersection [ (list, [ Intersection [ (list, bool_type.union) ] ]) ] ])
    polymoprhic_list_type.full

(* Represents `(X -> X -> Bool) -> X List -> X List -> Bool`, the type for the equal function *)
let binary_bool_list_op =
  map_type2
    (fun binary_poly_bool binary_list_bool ->
      [ Intersection [ (binary_poly_bool, binary_list_bool) ] ])
    binary_poly_bool_op binary_list_bool_op

(* Represents `X -> Bool`, the first part of the find function *)
let poly_bool_op = func_type ([ UnivTypeVar 0 ], bool_type.union)

(* Represents `X List -> X | None`, the second half of the find function *)
let list_extract_op =
  map_type
    (fun list ->
      [ Intersection [ (list, UnivTypeVar 0 :: none_label.stype.union) ] ])
    polymoprhic_list_type.full

(* Represents `(X -> Bool) -> X List -> X | None`, the type of the find function *)
let find_op =
  map_type2
    (fun poly_bool list_extract ->
      [ Intersection [ (poly_bool, list_extract) ] ])
    poly_bool_op list_extract_op

(* Polymoprhic function that prepends an element of arbitrary tpye to a list of that type *)
let cons =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            ( base_type (UnivTypeVar 0),
              Abstraction
                [
                  ( polymoprhic_list_type.full,
                    Abstraction
                      [
                        (name_label.stype, cons_label.term);
                        (val_label.stype, Variable 2);
                        (next_label.stype, Variable 1);
                      ] );
                ] );
          ]))

let cons_poly = UnivApplication (cons.term, base_type (UnivTypeVar 0))

(* Polymoprhic function that determines if a list is empty or not *)
let is_empty =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            (polymoprhic_list_type.non_empty, false_lambda.term);
            (empty_list.stype, true_lambda.term);
          ]))

(* Polymorphic function to get the first element of a list, or None if the list is empty *)
let head =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            ( polymoprhic_list_type.non_empty,
              Application (Variable 0, val_label.term) );
            (empty_list.stype, none_label.term);
          ]))

let head_poly =
  typed_term (UnivApplication (head.term, base_type (UnivTypeVar 0)))

let head_poly_nested1 =
  typed_term (UnivApplication (head.term, base_type (UnivTypeVar 1)))

(* Polymoprhic function to get all elements of a list except the first, or None is the list is empty *)
let tail =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            ( polymoprhic_list_type.non_empty,
              Application (Variable 0, next_label.term) );
            (empty_list.stype, none_label.term);
          ]))

let tail_poly =
  typed_term (UnivApplication (tail.term, base_type (UnivTypeVar 0)))

let tail_poly_nested1 = UnivApplication (tail.term, base_type (UnivTypeVar 1))
let fix_list_to_num = fix polymoprhic_list_type.full ind_integer
let fix_list_idx = fix polymoprhic_list_type.full idx_to_elt_op
let fix_unary_list = fix polymoprhic_list_type.full polymoprhic_list_type.full
let fix_binary_list = fix polymoprhic_list_type.full unary_list_op
let fix_filter = fix polymoprhic_list_type.full cond_to_list_op
let fix_fold = fix fold_step list_acc_op

let fix_map =
  fix (func_type ([ UnivTypeVar 1 ], [ UnivTypeVar 0 ])) list_transform_op

let fix_equal = fix binary_poly_bool_op binary_list_bool_op
let fix_find = fix poly_bool_op list_extract_op

let length =
  typed_term
    (UnivQuantifier
       (fix_list_to_num
          (Abstraction
             [
               ( list_to_num_op,
                 Abstraction
                   [
                     ( polymoprhic_list_type.non_empty,
                       Application
                         ( increment.term,
                           Application
                             ( Variable 1,
                               Application (tail_poly.term, Variable 0) ) ) );
                     (empty_list.stype, zero.term);
                   ] );
             ])))

(* TODO: update the fixed type so that we can infer that empty lists always return none *)
let nth =
  typed_term
    (UnivQuantifier
       (fix_list_idx
          (Abstraction
             [
               ( list_idx_op,
                 Abstraction
                   [
                     ( polymoprhic_list_type.non_empty,
                       Abstraction
                         [
                           (zero.stype, Application (head_poly.term, Variable 1));
                           ( ind_positive_number,
                             binary_apply (Variable 2)
                               (Application (tail_poly.term, Variable 1))
                               (Application (decrement.term, Variable 0)) );
                         ] );
                     ( empty_list.stype,
                       Abstraction [ (ind_natural_number, none_label.term) ] );
                   ] );
             ])))

let concat =
  typed_term
    (UnivQuantifier
       (fix_binary_list
          (Abstraction
             [
               ( binary_list_op,
                 Abstraction
                   [
                     ( polymoprhic_list_type.non_empty,
                       Abstraction
                         [
                           ( polymoprhic_list_type.full,
                             binary_apply cons_poly
                               (Application (head_poly.term, Variable 1))
                               (binary_apply (Variable 2)
                                  (Application (tail_poly.term, Variable 1))
                                  (Variable 0)) );
                         ] );
                     ( empty_list.stype,
                       Abstraction [ (polymoprhic_list_type.full, Variable 0) ]
                     );
                   ] );
             ])))

let concat_poly = UnivApplication (concat.term, base_type (UnivTypeVar 0))

let append =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            ( polymoprhic_list_type.full,
              Abstraction
                [
                  ( base_type (UnivTypeVar 0),
                    binary_apply concat_poly (Variable 1)
                      (binary_apply cons_poly (Variable 0) empty_list.term) );
                ] );
          ]))

let append_poly = UnivApplication (append.term, base_type (UnivTypeVar 0))

let reverse =
  typed_term
    (UnivQuantifier
       (fix_unary_list
          (Abstraction
             [
               ( unary_list_op,
                 Abstraction
                   [
                     ( polymoprhic_list_type.non_empty,
                       binary_apply append_poly
                         (Application
                            ( Variable 1,
                              Application (tail_poly.term, Variable 0) ))
                         (Application (head_poly.term, Variable 0)) );
                     (empty_list.stype, empty_list.term);
                   ] );
             ])))

let filter =
  typed_term
    (UnivQuantifier
       (fix_filter
          (Abstraction
             [
               ( filter_op,
                 Abstraction
                   [
                     ( polymoprhic_list_type.non_empty,
                       Abstraction
                         [
                           ( poly_to_bool_op,
                             Application
                               ( Abstraction
                                   [
                                     ( true_lambda.stype,
                                       binary_apply cons_poly
                                         (Application
                                            (head_poly.term, Variable 2))
                                         (binary_apply (Variable 3)
                                            (Application
                                               (tail_poly.term, Variable 2))
                                            (Variable 1)) );
                                     ( false_lambda.stype,
                                       binary_apply (Variable 3)
                                         (Application
                                            (tail_poly.term, Variable 2))
                                         (Variable 1) );
                                   ],
                                 Application
                                   ( Variable 0,
                                     Application (head_poly.term, Variable 1) )
                               ) );
                         ] );
                     ( empty_list.stype,
                       Abstraction [ (poly_to_bool_op, empty_list.term) ] );
                   ] );
             ])))

let map =
  typed_term
    (UnivQuantifier
       (UnivQuantifier
          (fix_map
             (Abstraction
                [
                  ( map_op,
                    Abstraction
                      [
                        ( func_type ([ UnivTypeVar 1 ], [ UnivTypeVar 0 ]),
                          Abstraction
                            [
                              ( polymorphic_list_type_nested1.non_empty,
                                binary_apply cons_poly
                                  (Application
                                     ( Variable 1,
                                       Application
                                         (head_poly_nested1.term, Variable 0) ))
                                  (binary_apply (Variable 2) (Variable 1)
                                     (Application (tail_poly_nested1, Variable 0)))
                              );
                              (empty_list.stype, empty_list.term);
                            ] );
                      ] );
                ]))))

let fold_left =
  typed_term
    (UnivQuantifier
       (UnivQuantifier
          (fix_fold
             (Abstraction
                [
                  ( fold_op,
                    Abstraction
                      [
                        ( fold_step,
                          Abstraction
                            [
                              ( base_type (UnivTypeVar 0),
                                Abstraction
                                  [
                                    ( polymorphic_list_type_nested1.non_empty,
                                      trinary_apply (Variable 3) (Variable 2)
                                        (binary_apply (Variable 2) (Variable 1)
                                           (Application
                                              ( head_poly_nested1.term,
                                                Variable 0 )))
                                        (Application
                                           (tail_poly_nested1, Variable 0)) );
                                    (empty_list.stype, Variable 1);
                                  ] );
                            ] );
                      ] );
                ]))))

let fold_left_poly_bool =
  typed_term
    (UnivApplication
       (UnivApplication (fold_left.term, base_type (UnivTypeVar 0)), bool_type))

let every =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            ( poly_to_bool_op,
              Abstraction
                [
                  ( polymoprhic_list_type.full,
                    trinary_apply fold_left_poly_bool.term
                      (Abstraction
                         [
                           ( bool_type,
                             Abstraction
                               [
                                 ( base_type (UnivTypeVar 0),
                                   binary_apply and_lambda.term (Variable 1)
                                     (Application (Variable 3, Variable 0)) );
                               ] );
                         ])
                      true_lambda.term (Variable 0) );
                ] );
          ]))

let exists =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            ( poly_to_bool_op,
              Abstraction
                [
                  ( polymoprhic_list_type.full,
                    trinary_apply fold_left_poly_bool.term
                      (Abstraction
                         [
                           ( bool_type,
                             Abstraction
                               [
                                 ( base_type (UnivTypeVar 0),
                                   binary_apply or_lambda.term (Variable 1)
                                     (Application (Variable 3, Variable 0)) );
                               ] );
                         ])
                      false_lambda.term (Variable 0) );
                ] );
          ]))

let equal =
  typed_term
    (UnivQuantifier
       (fix_equal
          (Abstraction
             [
               ( binary_bool_list_op,
                 Abstraction
                   [
                     ( binary_poly_bool_op,
                       Abstraction
                         [
                           ( empty_list.stype,
                             Abstraction
                               [
                                 (empty_list.stype, true_lambda.term);
                                 ( polymoprhic_list_type.non_empty,
                                   false_lambda.term );
                               ] );
                           ( polymoprhic_list_type.non_empty,
                             Abstraction
                               [
                                 (empty_list.stype, false_lambda.term);
                                 ( polymoprhic_list_type.non_empty,
                                   binary_apply and_lambda.term
                                     (binary_apply (Variable 2)
                                        (Application (head_poly.term, Variable 1))
                                        (Application (head_poly.term, Variable 0)))
                                     (trinary_apply (Variable 3) (Variable 2)
                                        (Application (tail_poly.term, Variable 1))
                                        (Application (tail_poly.term, Variable 0)))
                                 );
                               ] );
                         ] );
                   ] );
             ])))

let find =
  typed_term
    (UnivQuantifier
       (fix_find
          (Abstraction
             [
               ( find_op,
                 Abstraction
                   [
                     ( poly_bool_op,
                       Abstraction
                         [
                           (empty_list.stype, none_label.term);
                           ( polymoprhic_list_type.non_empty,
                             Application
                               ( Abstraction
                                   [
                                     ( true_lambda.stype,
                                       Application (head_poly.term, Variable 1)
                                     );
                                     ( false_lambda.stype,
                                       binary_apply (Variable 3) (Variable 2)
                                         (Application
                                            (tail_poly.term, Variable 1)) );
                                   ],
                                 Application
                                   ( Variable 1,
                                     Application (head_poly.term, Variable 0) )
                               ) );
                         ] );
                   ] );
             ])))

let fold_left_list_list =
  typed_term
    (UnivApplication
       ( UnivApplication (fold_left.term, polymoprhic_list_type.full),
         polymoprhic_list_type.full ))

let flatten =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            ( polymoprhic_nested_list_type.full,
              trinary_apply fold_left_list_list.term concat_poly empty_list.term
                (Variable 0) );
          ]))

(* List functions we should implement:
 * flatten
 *)
