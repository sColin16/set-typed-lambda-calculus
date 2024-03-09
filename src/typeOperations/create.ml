open Metatypes
open Helpers
open WellFounded

(** Constructs a recursive type from its constituent union type and recursive context *)
let build_recursive_type (union : union_type) (context : recursive_context) :
    recursive_type =
  { union; context }

(** Constructs a single entry in a recursive context *)
let build_recursive_def (kind : recursive_kind) (flat_union : flat_union_type) :
    recursive_def =
  { kind; flat_union }

(** Constructs a recursive context given a list of entries in the context.
    Verifies that each inductive type variable in the context is well-founded *)
let build_recursive_context (defs : (recursive_kind * flat_union_type) list) :
    recursive_context =
  let context =
    List.map (fun (kind, union) -> build_recursive_def kind union) defs
  in
  let valid_well_founded = is_valid_well_founded_context context in
  if valid_well_founded then context
  else raise (Invalid_argument "Context was not properly well-founded")

let expand_type_var (var_num : int) (context : recursive_context) =
  build_recursive_type (expand_type_var_to_union var_num context) context

let to_contractive_type (union : union_type) (context : recursive_context) =
  build_recursive_type (to_contractive_union union context) context

(** Constructs a recursive type from a union_type *)
let union_type (union_type : union_type) = build_recursive_type union_type []

(** Constructs a recursive type from a base_type *)
let base_type (base_type : base_type) = union_type [ base_type ]

(** Constructs a recursive type from an argument and return type *)
let func_type (unary_function : unary_function) =
  base_type (Intersection [ unary_function ])

(** Constructs a recursive type from a label string *)
let label_type (label : string) = base_type (Label label)
