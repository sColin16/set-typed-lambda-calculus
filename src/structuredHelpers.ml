open Structured.Metatypes
open Structured.TermTypes
open Structured.TypeOperations.Create
open Structured.TermOperations.Typing
open Structured.TypeOperations.Union
open TypeOperations.Context

type typed_term = { term : term; stype : structured_type }

let build_typed_term (term : term) (stype : structured_type) = { term; stype }
let get_type_unsafe term = Option.get (get_type term)
let get_typed_term_unsafe term = build_typed_term term (get_type_unsafe term)

let union_to_structured_type (union_type : union_type) =
  build_structured_type union_type []

let base_to_structured_type (base_type : base_type) =
  union_to_structured_type [ base_type ]

let func_to_structured_type (unary_function : unary_function) =
  base_to_structured_type (Intersection [ unary_function ])

let label_to_structured_type (label : string) =
  base_to_structured_type (Label label)

let get_type_intersection (types : structured_type list) : structured_type =
  let intersection =
    List.fold_left
      (fun acc_intersection next_type ->
        match next_type.union with
        | [ Intersection functions ] -> acc_intersection @ functions
        | _ -> raise (invalid_arg "a type wasn't just an intersection"))
      [] types
  in
  base_to_structured_type (Intersection intersection)

let get_flat_union_type (union_types : structured_type list) : flat_union_type =
  let union_type = get_type_union union_types in
  List.map
    (function
      | Label a -> FLabel a
      | Intersection a -> FIntersection a
      | UnivTypeVar a -> FUnivTypeVar a
      | UnivQuantification a -> FUnivQuantification a
      | RecTypeVar _ -> raise (Invalid_argument "got non-flat type"))
    union_type.union

(* Constructs the Z-combinator for a function of a given type, a fixed-point
    combinator for call-by-value semantics *)
let build_fix (arg_type : structured_type) (return_type : structured_type) =
  (* First, construct a function type from the arg type to the return type, taking
     care to properly join the contexts of the two types *)
  let (new_arg_type, new_return_type), shared_context =
    get_unified_type_context_pair arg_type return_type
  in
  let func_type =
    build_structured_type
      [ Intersection [ (new_arg_type, new_return_type) ] ]
      shared_context
  in
  (* Next, build the recursive definition that we'll add to the end of the joined context *)
  let rec_var_num = List.length shared_context in
  let fix_rec_def =
    build_recursive_def Coinductive
      [ FIntersection [ ([ RecTypeVar rec_var_num ], func_type.union) ] ]
  in
  (* Then add that definition to the end of the context so it has the number we assigned it *)
  let new_shared_context = List.append shared_context [ fix_rec_def ] in
  let fix =
    get_typed_term_unsafe
      (Abstraction
         [
           ( build_structured_type
               [ Intersection [ (func_type.union, func_type.union) ] ]
               new_shared_context,
             Application
               ( Abstraction
                   [
                     ( build_structured_type [ RecTypeVar rec_var_num ]
                         new_shared_context,
                       Application
                         ( Variable 1,
                           Abstraction
                             [
                               ( build_structured_type new_arg_type new_shared_context,
                                 Application
                                   ( Application (Variable 1, Variable 1),
                                     Variable 0 ) );
                             ] ) );
                   ],
                 Abstraction
                   [
                     ( build_structured_type [ RecTypeVar rec_var_num ]
                         new_shared_context,
                       Application
                         ( Variable 1,
                           Abstraction
                             [
                               ( build_structured_type new_arg_type new_shared_context,
                                 Application
                                   ( Application (Variable 1, Variable 1),
                                     Variable 0 ) );
                             ] ) );
                   ] ) );
         ])
  in
  fix

(* Fixes a provided abstraction with the given arg and return type *)
let fix (arg_type : structured_type) (return_type : structured_type)
    (term : term) =
  let fix_term = build_fix arg_type return_type in
  Application (fix_term.term, term)
