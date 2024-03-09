open Metatypes
open TermTypes
open TypeOperations.Create
open TermOperations.Typing
open TypeOperations.Union
open TypeOperations.Context
open TermOperations.Helpers

type typed_term = { term : term; rtype : recursive_type }

let build_typed_term (term : term) (rtype : recursive_type) = { term; rtype }
let get_type_unsafe term = Option.get (get_type term)
let typed_term term = build_typed_term term (get_type_unsafe term)

let type_intersection (types : recursive_type list) : recursive_type =
  let intersection =
    List.fold_left
      (fun acc_intersection next_type ->
        match next_type.union with
        | [ Intersection functions ] -> acc_intersection @ functions
        | _ -> raise (invalid_arg "a type wasn't just an intersection"))
      [] types
  in
  base_type (Intersection intersection)

let get_flat_union_type (union_types : recursive_type list) : flat_union_type =
  let union_type = type_union union_types in
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
let build_fix (arg_type : recursive_type) (return_type : recursive_type) =
  (* First, construct a function type from the arg type to the return type, taking
     care to properly join the contexts of the two types *)
  let (new_arg_type, new_return_type), shared_context =
    get_unified_type_context_pair arg_type return_type
  in
  let func_type =
    build_recursive_type
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
    typed_term
      (Abstraction
         [
           ( build_recursive_type
               [ Intersection [ (func_type.union, func_type.union) ] ]
               new_shared_context,
             Application
               ( Abstraction
                   [
                     ( build_recursive_type [ RecTypeVar rec_var_num ]
                         new_shared_context,
                       Application
                         ( Variable 1,
                           Abstraction
                             [
                               ( build_recursive_type new_arg_type
                                   new_shared_context,
                                 binary_apply (Variable 1) (Variable 1)
                                   (Variable 0) );
                             ] ) );
                   ],
                 Abstraction
                   [
                     ( build_recursive_type [ RecTypeVar rec_var_num ]
                         new_shared_context,
                       Application
                         ( Variable 1,
                           Abstraction
                             [
                               ( build_recursive_type new_arg_type
                                   new_shared_context,
                                 binary_apply (Variable 1) (Variable 1)
                                   (Variable 0) );
                             ] ) );
                   ] ) );
         ])
  in
  fix

(* Fixes a provided abstraction with the given arg and return type *)
let fix (arg_type : recursive_type) (return_type : recursive_type)
    (term : term) =
  let fix_term = build_fix arg_type return_type in
  Application (fix_term.term, term)
