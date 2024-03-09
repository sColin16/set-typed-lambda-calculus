open Metatypes
open Create
open Context

let map_type (func : union_type -> union_type) (input_type : structured_type) =
  let mapped_union = func input_type.union in
  build_structured_type mapped_union input_type.context

let map_type2 (func : union_type -> union_type -> union_type)
    (type1 : structured_type) (type2 : structured_type) =
  let (new_type1_union, new_type2_union), new_context =
    get_unified_type_context_pair type1 type2
  in
  let mapped_union = func new_type1_union new_type2_union in
  build_structured_type mapped_union new_context
