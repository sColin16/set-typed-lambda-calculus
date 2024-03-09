open Metatypes

type term =
  | Abstraction of (recursive_type * term) list
  | Application of term * term
  | Variable of int
  | Const of string
  | UnivQuantifier of term
  | UnivApplication of term * recursive_type

and value =
  | Closure of (recursive_type * term) list * environment
  | VUnivQuantifier of term
  | VConst of string

and environment = value list
