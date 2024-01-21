open Structured.Metatypes
open Structured.TermTypes
open Structured.TypeOperations.Create
open TypeOperations.Helpers
open TypeOperations.Context
open StructuredHelpers
open StructuredBool
open StructuredRecursive

let name_label = get_typed_term_unsafe (Const "Name")
let val_label = get_typed_term_unsafe (Const "Val")
let next_label = get_typed_term_unsafe (Const "Next")
let nil_label = get_typed_term_unsafe (Const "Nil")
let cons_label = get_typed_term_unsafe (Const "Cons")
let none_label = get_typed_term_unsafe (Const "None")

let polymoprhic_identity =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction [ (base_to_structured_type (UnivTypeVar 0), Variable 0) ]))

let polymorphic_double =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction
          [
            ( func_to_structured_type ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]),
              Abstraction
                [
                  ( base_to_structured_type (UnivTypeVar 0),
                    Application
                      (Variable 1, Application (Variable 1, Variable 0)) );
                ] );
          ]))

let polymorphic_quadruple =
  get_typed_term_unsafe
    (UnivQuantifier
       (Application
          ( UnivApplication
              ( polymorphic_double.term,
                func_to_structured_type ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ])
              ),
            UnivApplication
              (polymorphic_double.term, base_to_structured_type (UnivTypeVar 0))
          )))

let ind_poly_list_union = [ UnivQuantification [ RecTypeVar 0 ] ]

let ind_poly_list_context =
  [
    ( Inductive,
      [
        FIntersection [ (name_label.stype.union, nil_label.stype.union) ];
        FIntersection
          [
            (name_label.stype.union, cons_label.stype.union);
            (val_label.stype.union, [ UnivTypeVar 0 ]);
            (next_label.stype.union, [ RecTypeVar 0 ]);
          ];
      ] );
  ]

let empty_list =
  get_typed_term_unsafe (Abstraction [ (name_label.stype, nil_label.term) ])

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
  get_typed_term_unsafe (build_list_term_rec term_list)

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

let boolean_list_type = build_list_type_pair Inductive bool_type

let polymoprhic_list_type =
  build_list_type_pair Inductive (base_to_structured_type (UnivTypeVar 0))

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

(* Polymoprhic function that prepends an element of arbitrary tpye to a list of that type *)
let cons =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction
          [
            ( base_to_structured_type (UnivTypeVar 0),
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

(* Polymoprhic function that determines if a list is empty or not *)
let is_empty =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction
          [
            (polymoprhic_list_type.non_empty, false_lambda.term);
            (empty_list.stype, true_lambda.term);
          ]))

(* Polymorphic function to get the first element of a list, or None if the list is empty *)
let head =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction
          [
            ( polymoprhic_list_type.non_empty,
              Application (Variable 0, val_label.term) );
            (empty_list.stype, none_label.term);
          ]))

(* Polymoprhic function to get all elements of a list except the first, or None is the list is empty *)
let tail =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction
          [
            ( polymoprhic_list_type.non_empty,
              Application (Variable 0, next_label.term) );
            (empty_list.stype, none_label.term);
          ]))

let fix_list_to_num = fix polymoprhic_list_type.full ind_integer
let fix_list_idx = fix polymoprhic_list_type.full idx_to_elt_op
let fix_binary_list = fix polymoprhic_list_type.full unary_list_op

let length =
  get_typed_term_unsafe
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
                               Application
                                 ( UnivApplication
                                     ( tail.term,
                                       base_to_structured_type (UnivTypeVar 0)
                                     ),
                                   Variable 0 ) ) ) );
                     (empty_list.stype, zero.term);
                   ] );
             ])))

(* TODO: update the fixed type so that we can infer that empty lists always return none *)
let nth =
  get_typed_term_unsafe
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
                           ( zero.stype,
                             Application
                               ( UnivApplication
                                   ( head.term,
                                     base_to_structured_type (UnivTypeVar 0) ),
                                 Variable 1 ) );
                           ( ind_positive_number,
                             Application
                               ( Application
                                   ( Variable 2,
                                     Application
                                       ( UnivApplication
                                           ( tail.term,
                                             base_to_structured_type
                                               (UnivTypeVar 0) ),
                                         Variable 1 ) ),
                                 Application (decrement.term, Variable 0) ) );
                         ] );
                     ( empty_list.stype,
                       Abstraction [ (ind_natural_number, none_label.term) ] );
                   ] );
             ])))

let concat =
  get_typed_term_unsafe
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
                             Application
                               ( Application
                                   ( UnivApplication
                                       ( cons.term,
                                         base_to_structured_type (UnivTypeVar 0)
                                       ),
                                     Application
                                       ( UnivApplication
                                           ( head.term,
                                             base_to_structured_type
                                               (UnivTypeVar 0) ),
                                         Variable 1 ) ),
                                 Application
                                   ( Application
                                       ( Variable 2,
                                         Application
                                           ( UnivApplication
                                               ( tail.term,
                                                 base_to_structured_type
                                                   (UnivTypeVar 0) ),
                                             Variable 1 ) ),
                                     Variable 0 ) ) );
                         ] );
                     ( empty_list.stype,
                       Abstraction [ (polymoprhic_list_type.full, Variable 0) ]
                     );
                   ] );
             ])))

let append =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction
          [
            ( polymoprhic_list_type.full,
              Abstraction
                [
                  ( base_to_structured_type (UnivTypeVar 0),
                    Application
                      ( Application
                          ( UnivApplication
                              ( concat.term,
                                base_to_structured_type (UnivTypeVar 0) ),
                            Variable 1 ),
                        Application
                          ( Application
                              ( UnivApplication
                                  ( cons.term,
                                    base_to_structured_type (UnivTypeVar 0) ),
                                Variable 0 ),
                            empty_list.term ) ) );
                ] );
          ]))

(* List functions we should implement:
 * reverse
 * flatten
 * equal
 * map
 * filter
 * fold_left/fold_right
 * find (return element and/or index)
 * forall/exists
 *)
