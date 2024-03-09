open Metatypes
open TermOperations.ValToTerm
open TermOperations.Eval
open TypeOperations.Subtype

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let evaluates_to term value = value_to_term (eval term) = value

let is_equivalent_type (t1 : structured_type) (t2 : structured_type) =
  is_subtype t1 t2 && is_subtype t2 t1

let is_strict_subtype (t1 : structured_type) (t2 : structured_type) =
  is_subtype t1 t2 && not (is_subtype t2 t1)
