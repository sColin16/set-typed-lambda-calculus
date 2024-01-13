open Structured.Metatypes
open Structured.TermTypes
open Structured.TypeOperations.Create
open TypeOperations.Helpers
open StructuredHelpers
open StructuredBool

let name_label = get_typed_term_unsafe (Const "Name")
let val_label = get_typed_term_unsafe (Const "Val")
let next_label = get_typed_term_unsafe (Const "Next")
let nil_label = get_typed_term_unsafe (Const "Nil")
let cons_label = get_typed_term_unsafe (Const "Cons")

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

(* The polymoprhic cons function that prepends an element of arbitrary tpye to a list of that type *)
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

(* Polymoprhic is_empty function, which checks if a list is empty or not *)
let is_empty =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction
          [
            (polymoprhic_list_type.non_empty, false_lambda.term);
            (empty_list.stype, true_lambda.term);
          ]))
