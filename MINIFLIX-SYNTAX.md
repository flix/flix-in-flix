# MiniFlix Surface Syntax Draft

This file proposes a small declarative syntax for writing type-checker fixtures
against the current `flix-in-flix` core. The goal is not full Flix syntax. The
goal is a tiny surface language that maps directly onto the current AST and
constraint environment:

- `TopLevelDecl = (Id, Scheme[Type], Expr)`
- `ConstrEnv` for traits, instances, super-traits, and associated equalities
- `Type` for constructors, functions, associated applications, and effects
- `Constr` for trait constraints and equality constraints

## Design Goals

- Small enough to parse in a single pass.
- Declarative enough to write tests without constructing AST nodes by hand.
- Close to familiar Flix notation where possible.
- Explicit about effects.
- Use a single associated-member syntax with kind ascription to distinguish
  ordinary associated types from associated effects.

## Overview

```text
trait Eq[a]
trait Ord[a] <: Eq[a]
trait Show[a]
trait Collect[a] {
  type Elem
  type Visit: Eff
}
trait Functor[f: Type -> Type]
enum Handle[h: Eff -> Type]

instance Show[a] => Eq[a]
instance Eq[a] => Ord[a]
instance Collect[List[a]] {
  type Elem = a
  type Visit: Eff = Read + Write
}

enum Option[t]
enum Fix[f: Type -> Type]
enum Higher[k: (Type -> Type) -> Type]

def id: forall a. a -> a \ {} = \x -> x
def main: Unit = do IO
def runMain: Unit = run main without IO
```

## Grammar Sketch

```ebnf
Program      ::= Item*

Item         ::= TraitDecl
               | EnumDecl
               | InstanceDecl
               | TopDecl

TraitDecl    ::= "trait" UIdent "[" TyBinder "]" SuperClause? TraitBody?
SuperClause  ::= "<:" TraitHead
TraitBody    ::= "{" AssocDecl* "}"

AssocDecl    ::= "type" UIdent AssocResultKind?

EnumDecl     ::= "enum" UIdent "[" TyBinders? "]"

InstanceDecl ::= "instance" Context "=>" TraitHead
               | "instance" TraitHead
               | "instance" Context "=>" TraitHead InstBody
               | "instance" TraitHead InstBody
InstBody     ::= "{" AssocEqDecl* "}"

AssocResultKind ::= ":" Kind
AssocEqDecl  ::= "type" UIdent AssocResultKind? "=" AssocValue
AssocValue   ::= Type
               | Effect

TopDecl      ::= "def" ident ":" Scheme "=" Expr

Scheme       ::= ForallPart? QualType
ForallPart   ::= "forall" TyBinders "."
QualType     ::= Context "=>" Type
               | Type

Context      ::= Constraint ("," Constraint)*
Constraint   ::= TraitHead
               | Type "~" Type

TraitHead    ::= UIdent "[" Type "]"

AssocApp     ::= UIdent "[" Type "]"

TyBinders    ::= TyBinder ("," TyBinder)*
TyBinder     ::= ident
               | ident ":" Kind

Kind         ::= KindAtom "->" Kind
               | KindAtom

KindAtom     ::= "Type"
               | "Eff"
               | "(" Kind ")"

Type         ::= FunType
FunType      ::= AppType "->" Type "\" Effect
               | AppType "->" Type
               | AppType

AppType      ::= TypeAtom
               | UIdent "[" TypeList? "]"
               | AssocApp

TypeList     ::= Type ("," Type)*

TypeAtom     ::= ident
               | UIdent
               | "(" Type ")"

Effect       ::= EffectSum
EffectSum    ::= EffectSum "+" EffectProd
               | EffectSum "^" EffectProd
               | EffectProd

EffectProd   ::= EffectProd "&" EffectUnary
               | EffectUnary

EffectUnary  ::= "~" EffectUnary
               | "{}"
               | UIdent
               | ident
               | AssocApp
               | "(" Effect ")"

Expr         ::= ident
               | IntLit
               | BoolLit
               | CharLit
               | "()"
               | "\" ident "->" Expr
               | Expr Expr
               | "if" Expr "then" Expr "else" Expr
               | "do" UIdent
               | "run" Expr "without" UIdent
               | "(" Expr ")"
```

## Core Forms

### 1. Expressions

Use a minimal expression language that matches the current `Expr` cases:

```text
x
42
true
'a'
()
\x -> x
f x
if c then t else f
do IO
run e without IO
```

Suggested desugaring:

- `x` -> `Expr.Var("x")`
- `42` -> `Expr.Lit(Type.int32())`
- `true` -> `Expr.Lit(Type.bool())`
- `'a'` -> `Expr.Lit(Type.char())`
- `()` -> `Expr.Lit(Type.unit())`
- `\x -> e` -> `Expr.Lam("x", e)`
- `f x` -> `Expr.Ap(f, x)`
- `if c then t else f` -> `Expr.IfElse(c, t, f)`
- `do IO` -> `Expr.Do("IO")`
- `run e without IO` -> `Expr.RunWith(e, "IO")`

Note: literals are type-only test literals. Their runtime value is ignored by
the current core checker.

### 2. Trait Declarations With Super-Traits

Use:

```text
trait Ord[a] <: Eq[a]
trait Show[a]
trait Collect[a] {
  type Elem
  type Visit: Eff
}
trait Functor[f: Type -> Type]
```

Suggested meaning:

- `trait Show[a]`
  - `ConstrEnv.addClass("Show", env)`
- `trait Ord[a] <: Eq[a]`
  - `ConstrEnv.addClass("Ord", env)`
  - `ConstrEnv.addSuper("Ord", "Eq", env)`
- `trait Collect[a] { ... }`
  - `ConstrEnv.addClass("Collect", env)`
  - declares associated members that may later receive equations in instances
- `trait Functor[f: Type -> Type]`
  - `ConstrEnv.addClass("Functor", env)`
  - the type parameter is explicitly kinded as higher-kinded

For now, the superclass relation is name-based in the core checker. The single
parameter `a` is still worth keeping in the syntax because it makes
declarations readable and matches the current class constraint representation.

### 3. Instance Declarations With Context And Head

Use the standard qualified shape:

```text
instance Eq[Int32]
instance Show[a] => Eq[a]
instance Eq[a], Show[a] => Ord[a]
instance Collect[List[a]] {
  type Elem = a
  type Visit: Eff = IO
}
```

Interpretation:

- The right side of `=>` is the instance head.
- The left side of `=>` is the instance context.
- If there is no `=>`, the context is empty.
- An optional instance body carries unified associated-member equations.

Suggested desugaring:

```text
instance Show[a] => Eq[a]
```

becomes an `Inst` whose:

- head is `("Eq", Type.Var(a))`
- context is `Constr.Class("Show", Type.Var(a)) :: Nil`

This is a direct surface form for:

```flix
Inst.Inst(Qual.Qual(
    Constr.Class("Show", Type.Var(a)) :: Nil,
    ("Eq", Type.Var(a))
))
```

And:

```text
instance Collect[List[a]] {
  type Elem = a
  type Visit: Eff = Read + Write
}
```

adds:

- an `Inst` for the trait head `Collect[List[a]]`
- an associated type equality for `Elem[List[a]] = a`
- an associated effect equality for `Visit[List[a]]: Eff = Read + Write`

### 4. Higher-Kinded Types And Kind Scription

Use surface kinds:

```text
Type
Eff
Type -> Type
Eff -> Type
(Type -> Type) -> Type
```

Suggested meaning:

- `Type` is the surface name for the core kind `Kind.Star`
- `Eff` is the surface name for the core kind `Kind.Eff`
- `k1 -> k2` is the surface form for `Kind.KFun(k1, k2)`

The arrow is right-associative, so:

```text
Type -> Type -> Type
```

means:

```text
Type -> (Type -> Type)
```

Use kind ascriptions on binders:

```text
trait Functor[f: Type -> Type]
enum Handle[h: Eff -> Type]
enum Fix[f: Type -> Type]
enum Higher[k: (Type -> Type) -> Type]
def wrap: forall f: Type -> Type, a. a -> f[a] \ {} = \x -> x
```

This gives you the higher-kinded forms you asked for, including:

```text
Eff -> Type
(Type -> Type) -> Type
```

Kind scription is only needed on binders and associated-member result kinds in
the first version:

- trait parameters
- enum parameters
- `forall` parameters
- associated member result kinds

If no kind is written, the default is `Type`.

### 5. Unified Associated Member Declarations

Declare associated members inside a trait with a single `type` form:

```text
trait Collect[a] {
  type Elem
  type Visit: Eff
}
trait Functor[f: Type -> Type] {
  type Wrapped
}
```

This keeps the declaration of the associated member attached to the trait, but
the actual equations are supplied by instances.

Suggested meaning:

- `type Elem`
  - declares an associated type family named `Elem`
- `type Visit: Eff`
  - declares an associated effect family named `Visit`
- `type Wrapped`
  - declares an associated type family over a higher-kinded parameter

If the result kind is omitted, it defaults to `Type`.

The trait binder is already in scope for these declarations, so it does not
need to be repeated. For example:

- inside `trait Collect[a]`, `type Elem` implicitly means a member associated
  with the trait parameter `a`
- inside `trait Functor[f: Type -> Type]`, `type Wrapped` implicitly ranges over
  the trait parameter `f`

The current core does not yet store trait ownership of associated members
explicitly, so this part is mainly a surface-language discipline.

### 6. Associated Equalities Inside Instances

Use instance-local equality rules:

```text
instance Collect[List[a]] {
  type Elem = a
  type Visit: Eff = Read + Write
}
```

This couples associated equalities to the instance that introduces them at the
surface level. Internally, the equalities can still lower to separate
`ConstrEnv.addAssocEq(...)` entries after the instance body is parsed.

Suggested lowering:

- inside `instance Collect[List[a]] { ... }`,
  `type Elem = a`
  - the omitted left-hand argument is inherited from the instance head, so the
    logical equality is `Elem[List[a]] = a`
  - left side becomes `Type.Assoc(Tyassoc.Tyassoc("Elem", List[a], Kind.Star))`
  - stored with `ConstrEnv.addAssocEq("Elem", (lhs, rhs), env)`
- inside `instance Collect[List[a]] { ... }`,
  `type Visit: Eff = Read + Write`
  - the omitted left-hand argument is inherited from the instance head, so the
    logical equality is `Visit[List[a]]: Eff = Read + Write`
  - left side becomes `Type.Assoc(Tyassoc.Tyassoc("Visit", List[a], Kind.Eff))`
  - stored with `ConstrEnv.addAssocEq("Visit", (lhs, rhs), env)`

Parsing rule:

- the left-hand argument of an associated equality is implicit and always comes
  from the enclosing instance head
- if the associated member result kind is omitted, treat it as `Type`
- if the result kind is `Eff`, parse the right-hand side as an effect formula
- otherwise parse the right-hand side as a type expression

This gives the surface syntax the grouping you want while still targeting the
same reduction machinery underneath.

### 7. Basic Enum Type Constructors

Use square-bracket application:

```text
Int32
Bool
List[Int32]
Option[a]
Result[Int32, Bool]
f[a]
Fix[List]
```

This should map to nested `Type.Ap` nodes, schematically:

- `List[Int32]` -> `Type.Ap(List, Int32)`
- `Result[Int32, Bool]` -> `Type.Ap(Type.Ap(Result, Int32), Bool)`
- `f[a]` -> `Type.Ap(f, a)`
- `Fix[List]` -> `Type.Ap(Fix, List)`

This syntax is simple and works for ordinary enum-like type constructors.

### 8. Basic Enum Declarations

Use:

```text
enum Option[t]
enum Result[e, t]
enum Map[k, v]
enum Handle[h: Eff -> Type]
enum Fix[f: Type -> Type]
enum Higher[k: (Type -> Type) -> Type]
```

This is intentionally minimal. For the current type-checker fixtures, an enum
declaration only needs to introduce a named type constructor and its arity.

Suggested meaning:

- `enum Option[t]`
  - introduces a type constructor `Option` of kind `* -> *`
- `enum Result[e, t]`
  - introduces a type constructor `Result` of kind `* -> * -> *`
- `enum Handle[h: Eff -> Type]`
  - introduces a type constructor `Handle` of kind `(Eff -> Type) -> Type`
- `enum Fix[f: Type -> Type]`
  - introduces a type constructor `Fix` of kind `(Type -> Type) -> Type`
- `enum Higher[k: (Type -> Type) -> Type]`
  - introduces a type constructor `Higher` of kind `((Type -> Type) -> Type) -> Type`

If you later want value constructors, you can extend this to:

```text
enum Option[t] {
  case None
  case Some(t)
}
```

but that is not required for the current core type-checker tests.

### 9. Basic Function Type Constructors

Use:

```text
Int32 -> Bool
Int32 -> Bool \ IO
List[a] -> Bool \ (Read + Write)
```

Rules:

- `a -> b` is shorthand for `a -> b \ {}`
- `a -> b \ ef` maps directly to `Type.mkArrow(a, ef, b)`

Examples:

- `Int32 -> Bool`
  - `Type.mkArrow(Int32, {}, Bool)`
- `Int32 -> Bool \ IO`
  - `Type.mkArrow(Int32, IO, Bool)`

This gives you the notation:

```text
Input -> Output \ EffFormula
```

### 10. Top-Level Declarations

Use:

```text
def x: Int32 = 42
def id: forall a. a -> a \ {} = \x -> x
def eqId: forall a. Eq[a] => a -> Bool \ {} = \x -> true
def lift: forall f: Type -> Type, a. a -> f[a] \ {} = \x -> x
```

This maps directly to:

- declaration name
- programmer-written `Scheme[Type]`
- expression body

So:

```text
def x: Int32 = 42
```

corresponds to:

```flix
("x", Scheme.newUnqual(Type.int32()), Expr.Lit(Type.int32()))
```

### 11. Basic Effect Formulas

Effects should use the same operators already present in `Type`:

```text
{}
IO
Read + Write
Read & ~Write
X ^ Y
(Read + Write) & ~Network
Visit[List[a]]
```

Suggested operator meanings:

- `{}`: empty effect
- `+`: union
- `&`: intersection
- `^`: xor
- `~`: complement

Suggested precedence:

1. `~`
2. `&`
3. `+` and `^`

Suggested desugaring:

- `{}` -> `Type.efEmpty()`
- `IO` -> `Type.efConstant("IO")`
- `Read + Write` -> `Type.mkUnion(Read, Write)`
- `Read & ~Write` -> `Type.mkIntersect(Read, Type.mkCompl(Write))`
- `Visit[List[a]]` -> `Type.Assoc(Tyassoc.Tyassoc("Visit", List[a], Kind.Eff))`

## Worked Example

```text
trait Eq[a]
trait Ord[a] <: Eq[a]
trait Show[a]
trait Collect[a] {
  type Elem
  type Visit: Eff
}
trait Functor[f: Type -> Type]
enum Handle[h: Eff -> Type]

instance Eq[Int32]
instance Eq[a] => Ord[a]
instance Collect[List[a]] {
  type Elem = a
  type Visit: Eff = IO
}

enum Option[t]
enum Fix[f: Type -> Type]
enum Higher[k: (Type -> Type) -> Type]

def id: forall a. a -> a \ {} = \x -> x
def main: Unit = do IO
def safeMain: Unit = run main without IO
```

This exercises:

- expression syntax
- higher-kinded binders and kind scription
- trait declarations
- superclass syntax
- unified associated-member declarations
- instance head and context
- associated equalities inside instances
- enum declarations
- top-level declarations
- function types
- effect handling

## Recommended Parsing Restrictions

To keep the first parser small, I would enforce these restrictions:

- Trait heads and instance heads have exactly one type argument: `Eq[a]`,
  `Collect[List[a]]`.
- Super-trait clauses use the same single-parameter shape: `trait Ord[a] <: Eq[a]`.
- Kind scription only appears on binders, not arbitrary type expressions.
- Associated-member result kinds use `: Kind` and default to `Type` when omitted.
- Omitted binder kinds default to `Type`.
- Kind arrows are right-associative.
- No infix user-defined type constructors.
- Enum declarations introduce arity only, not value constructors.
- Associated member declarations inside traits are signatures only and reuse the
  enclosing trait binder implicitly.
- Associated equalities only appear inside instance bodies.
- Instance bodies contain equations only, not nested instance declarations.
- Effects in types appear only in `Input -> Output \ Eff`.
- Effect operations in expressions are limited to `do E` and `run e without E`.
- Keep application left-associative for both types and expressions.

## Minimal Test Corpus

```text
trait Eq[a]
trait Ord[a] <: Eq[a]
trait Show[a]
trait Collect[a] {
  type Elem
  type Visit: Eff
}
trait Functor[f: Type -> Type]
enum Handle[h: Eff -> Type]

instance Eq[Int32]
instance Eq[a] => Ord[a]
instance Collect[List[a]] {
  type Elem = a
  type Visit: Eff = IO
}

enum Option[t]
enum Fix[f: Type -> Type]
enum Higher[k: (Type -> Type) -> Type]

def x: Int32 = 42
def id: forall a. a -> a \ {} = \x -> x
def lift: forall f: Type -> Type, a. a -> f[a] \ {} = \x -> x
def choose: Bool -> Int32 -> Int32 -> Int32 \ {} =
  \b -> \t -> \f -> if b then t else f
def main: Unit = do IO
def safeMain: Unit = run main without IO
```
