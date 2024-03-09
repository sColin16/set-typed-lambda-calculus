open Metatypes
open TypeOperations.MapType
open ExampleHelpers
open Recursive

(* TODO: create some helper functions to make existential encoding easier to use *)

let new_label = typed_term (Const "new")
let get_label = typed_term (Const "get")
let inc_label = typed_term (Const "inc")

(* Represents the type `CounterModule = {new: Counter, get: Counter -> Nat, inc: Counter -> Counter}` *)
let counter_module =
  map_type
    (fun int ->
      [
        Intersection
          [
            (new_label.rtype.union, [ UnivTypeVar 0 ]);
            ( get_label.rtype.union,
              [ Intersection [ ([ UnivTypeVar 0 ], int) ] ] );
            ( inc_label.rtype.union,
              [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ] );
          ];
      ])
    ind_integer

(* Represents `forall Counter. (CounterModule -> Y)`, the "continuation" at the
   core of the polymorphic encoding of existential types *)
let counter_continuation =
  map_type
    (fun counter_module_union ->
      [
        UnivQuantification
          [ Intersection [ (counter_module_union, [ UnivTypeVar 1 ]) ] ];
      ])
    counter_module

(*
  Represents the existential package type:
  `{exists Counter, CounterModule}`
  encoded using polymoprhism as:
  `forall Y.((forall Counter.(CounterModule -> Y) -> Y)`
*)
let counter_package_type =
  map_type
    (fun counter_continuation_union ->
      [
        UnivQuantification
          [ Intersection [ (counter_continuation_union, [ UnivTypeVar 0 ]) ] ];
      ])
    counter_continuation

(* Term representing a counter ADT, encoded using polymoprhism, using Int as the implementation for Counter *)
let counter_adt =
  typed_term
    (UnivQuantifier
       (Abstraction
          [
            ( counter_continuation,
              Application
                ( UnivApplication (Variable 0, ind_integer),
                  Abstraction
                    [
                      (new_label.rtype, one.term);
                      ( get_label.rtype,
                        Abstraction [ (ind_integer, Variable 0) ] );
                      ( inc_label.rtype,
                        Abstraction
                          [
                            ( ind_integer,
                              Application (increment.term, Variable 0) );
                          ] );
                    ] ) );
          ]))
