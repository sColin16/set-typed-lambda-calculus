type 'a union = 'a list
type 'a intersection = 'a list

type structured_type = { union : union_type; context : recursive_context }
and union_type = base_type list

and base_type =
  | Label of string
  | Intersection of unary_function list
  | RecTypeVar of int
  | UnivTypeVar of int
  | UnivQuantification of union_type

and unary_function = union_type * union_type
and recursive_context = recursive_def list
and flat_union_type = flat_base_type list

and flat_base_type =
  | FLabel of string
  | FIntersection of unary_function list
  | FUnivTypeVar of int
  | FUnivQuantification of union_type

and recursive_def = { kind : recursive_kind; flat_union : flat_union_type }
and recursive_kind = Inductive | Coinductive

module TypeVarUnionSet = Set.Make (struct
  type t = int * union_type

  let compare = compare
end)
