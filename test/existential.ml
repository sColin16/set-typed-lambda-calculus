open SetTypedLambdaExample.Existential
open SetTypedLambdaExample.Recursive
open SetTypedLambdaExample.ExampleHelpers
open TypeOperations.Subtype
open TestHelpers

let get_new_counter =
  typed_term
    (Application
       ( UnivApplication (counter_adt.term, ind_integer),
         UnivQuantifier
           (Abstraction
              [
                ( counter_module,
                  Application
                    ( Application (Variable 0, get_label.term),
                      Application (Variable 0, new_label.term) ) );
              ]) ))

let get_incremented_counter =
  typed_term
    (Application
       ( UnivApplication (counter_adt.term, ind_integer),
         UnivQuantifier
           (Abstraction
              [
                ( counter_module,
                  Application
                    ( Application (Variable 0, get_label.term),
                      Application
                        ( Application (Variable 0, inc_label.term),
                          Application (Variable 0, new_label.term) ) ) );
              ]) ))

let () =
  test "Counter ADT has expected type"
    (is_subtype counter_adt.rtype counter_package_type)

let () =
  test "Get new counter evaluates to 1"
    (evaluates_to get_new_counter.term one.term)

let () =
  test "Get incremented counter evaluates to 2"
    (evaluates_to get_incremented_counter.term two.term)
