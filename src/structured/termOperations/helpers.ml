open TermTypes

(** Generates a term to apply two arguments to a function, for convenience *)
let binary_apply (func : term) (arg1 : term) (arg2 : term) =
  Application (Application (func, arg1), arg2)
