# {λ} Set-Typed Lambda Calculus
A typed lambda calculus with a set-theoretic type system, that serves as the
theoretical basis for other languages with set-theoretic type systems

## Overview
Set-typed Lambda Calculus is a simply-typed lambda calculus, augmented with the
following features:
- Singleton base types
- Union types
- Intersection types
- Inductive and Coinductive types
- Parametric Polymoprhism
- Structural subtyping

The combination of these features, particularly union and intersection types,
creates a powerful type system whose types behave like sets, which makes for
an intuitive type system. The type system can represent a wide range of common
programming language constructs, but at a more fundamental level, which allows
for some interesting properties.

Here are some of the language constructs Set-Typed Lambda Calculus can represent:
- Booleans
- Enums
- Sum types (a.k.a. tagged unions)
- Product types (e.g. tuples, records)
- Nominative types (i.e. subtyping without structural typing properties)
- Integers/strings of arbitrary size
- Functions
  - Including overloaded functions (ad-hoc polymorphism)
  - Including recursive functions
- Classes
- Polymoprhic data structures (e.g. lists, sets)
- Existential types (e.g. ML modules)

Typed lambda calculi typically represent sum and product type as first-class
language constructs, which have specialized semantics and typing rules. For
example, record types typically have special width and depth subtyping rules
that are only applicable to records.

In Set-Typed Lambda Calculus, however, sum and product types are derived types,
and their semantics and typing rules are derived from more fundamental
constructs of the language

Record types are represented as the intersection of function types, and width
and depth subtyping arise from the interaction of the typing rules for
intersections and functions

Tagged unions are represented as the union of tagged types, where tagging is
accomplished through intersection. No special rules are needed to type tagged
unions, their properties emerge from the interaction of the building blocks
of the type system

These more fundamental building blocks allow for interesting use-cases. For
example, optional types can be represented as a simple union of the underlying
type and a special "None" label. By their nature, the underlying type is a
subtype of the optional type, which isn't typically the case in other languages

## Features on the Roadmap
### Core Language Features
Features that are core parts of the calculus, from which more advanced
constructs can be built
- Bounded polymorphism to assert properties of universal and existentially
quantified types
- Intersections of quantifiers, as a generalization of abstraction
intersections, and as a means to implement provide different implementations for
polymoprhic types, depending on the argument type
- Higher kinded-types and type-level programming

### External Language Features
Features that would be included in a higher-level language, to more directly
provide familiar language constructs
- AST's that support named terms, instead of De Bruijn encodings of terms
- Lexer/Parser to support writing programs outside of the embedded context of OCaml's language
- Let constructs to enable more intuitively expressive programs
  - These simply provide syntactic sugar over abstractions
- Type ascription to abstract details of a type away and support information hiding
- Type aliases for more expressiveness surrounding types
- Effect systems to augment the type system and express when exceptions are
  thrown or impure operations occur
- Type inference to avoid the requirement for type annotations everywhere

## Inspiration
Set-Typed Lambda Calculus is inspired by TypeScript's set-theoretic and
structurally-typed type system, which includes union, intersection, and literal
types. In fact, Set-Typed Lambda Calculus was born from an attempt to formalize
the sorts of type constructs that TypeScript provides

## Open Questions
- How to efficiently implement the type-based branching of lambda terms. It is similar
  in nature to pattern matching, but the expressivness of the type system adds complexity
  and opens questions about the extent to which a value can be introspected to determine
  a more specific type, especially in the context of impure computation
- What sorts type inference are possible and how do they interact with advanced language
  constructs. Is a full type inference ala Hindley-Milner possibe? Would such type inference
  require universal quantification type contructs? Or would universal type constructs interfere
  with such type inference? Would bidirectional type inference be possible? Would that eliminate
  the need for universal quantification or be compatible with it? How would we identify where
  type annotations are required in such a case?
