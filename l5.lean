set_option autoImplicit false

/-
# Product types and sum types

Until now, most of our functions have returned a single natural number or Boolean.
In this lecture we learn two fundamental ways of constructing richer types:

* a **product** `A × B` contains both an `A` and a `B`;
* a **sum** `A ⊕ B` contains either an `A` or a `B`.

We will also meet two closely related types:
* `Unit`, which can be viewed as a product with no components;
* `Option A`, which represents either a value of type A or the absence of such a value.

By the end of the lecture, you should be able to:

* construct pairs and inspect their components;
* use pattern matching on pairs and nested tuples;
* explain the difference between curried and uncurried functions;
* use structures as products with named components;
* construct and inspect values of sum types;
* use `Option Nat` for partial computations returning natural numbers;
* prove properties involving the new types.

The symbols `A` and `B` in the comments stand informally for arbitrary types.
In the Lean code, however, we deliberately work with concrete types such as
`Nat`, `Bool`, and `String`. The next lecture will explain how to write one
definition that works uniformly for arbitrary types: this is **polymorphism**.

Exercise difficulties use the same relative scale as in previous lectures:

* **1/4:** one direct idea;
* **2/4:** two ideas must be combined;
* **3/4:** a more substantial construction or proof;
* **4/4:** an optional challenge.
-/


section Product_types

/-
## Product types

Suppose that a computation must return two results. We could define two
separate functions, but that may repeat the same computation.
A product type lets us package the two results together.

If `A` and `B` are types, then

    A × B

is the type of pairs whose first component has type `A` and whose second
component has type `B`. Type `\times` to enter the symbol `×`.

The notation `(a, b)` constructs a pair:
-/

def myPair : Nat × Bool := (3, true)

/- This is equivalent to using the explicit **introduction** operator `Prod.mk`: -/

def myPair₂ : Nat × Bool := Prod.mk 3 true

example : myPair = myPair₂ := by rfl

/-
The two components of a pair may have the same type or different types.
Products can also be **nested**, and functions may return pairs.
-/


/- __Exercise (difficulty: 1/4)__ Construct values of the given types.
Notice where the parentheses occur. -/

example : Nat × Nat           := (2, 2)
example : (Nat × Bool) × Nat  := ((1, true), 0)
example : Nat × (Bool × Nat)  := (0, (false, 2))
example : Nat → (Nat × Nat)  := (fun x => (x + 1, x - 1))
example : Nat → (Nat × Bool) := (fun x => (x + 1, true))

/-
Parentheses matter. In general,

    (A × B) × C

and

    A × (B × C)

are different types, with differently shaped values:

    ((a, b), c) : (A × B) × C
    (a, (b, c)) : A × (B × C)
-/


section Projections

/-
### Projections

If `p : A × B`, its two components can be obtained using:

    p.1 : A
    p.2 : B

Constructing `(a, b)` is an **introduction** operation for products.
Projections are **elimination** operations: they extract the elements in a pair.
-/

#eval myPair.1
#eval myPair.2

def swapNatBool (p : Nat × Bool) : Bool × Nat :=
  (p.2, p.1)

example : swapNatBool (7, true)  = (true, 7) := by rfl
example : swapNatBool (0, false) = (false, 0) := by rfl


/- __Exercise (difficulty: 1/4)__ Define the following functions using projections. -/

def sumComponents (p : Nat × Nat) : Nat :=
  p.1 + p.2

def keepFirstAndDoubleSecond (p : Nat × Nat) : Nat × Nat :=
  (p.1, 2 * p.2)

example : sumComponents (3, 4) = 7 := by rfl
example : keepFirstAndDoubleSecond (3, 4) = (3, 8) := by rfl

end Projections



section Pattern_matching

/-
Instead of projecting the components separately, we can expose both of them at once by pattern matching:
-/

#eval match myPair with
  | (n, _) => n

/-
We define an alternative version of `swapNatBool` using pattern matching:
-/

def swapNatBool₂ : Nat × Bool → Bool × Nat
  | (n, b) => (b, n)

/- The two versions of `swapNatBool` are equivalent. -/

example (p : Nat × Bool): swapNatBool₂ p  = swapNatBool p := by rfl

/- __Exercise (difficulty: 1/4)__ Define the following functions using pattern matching. -/

def addPair : Nat × Nat → Nat
  | (n, m) => n + m

def mulPair : Nat × Nat → Nat
  | (n, m) => n * m

example : addPair (3, 4) = 7  := by rfl
example : mulPair (3, 4) = 12 := by rfl

/- __Exercise (difficulty: 1/4)__ The Boolean component chooses which number to return. -/

def chooseFromPair : (Nat × Nat) × Bool → Nat
  | ((n, m), b) => if b then n else m

example : chooseFromPair ((10, 20), true)  = 10 := by rfl
example : chooseFromPair ((10, 20), false) = 20 := by rfl

end Pattern_matching


section Tuples

/-
### Tuples are nested pairs

Lean uses nested products to represent tuples with more than two components:

    A × B × C    means    A × (B × C)
    (a, b, c)    means    (a, (b, c))

The notation hides the nesting, but projections reveal it:
-/

example : (7, 8, 9) = (7, (8, 9)) := by rfl
example : (7, 8, 9).1 = 7 := by rfl
example : (7, 8, 9).2 = (8, 9) := by rfl
example : (7, 8, 9).2.1 = 8 := by rfl


/- __Exercise (difficulty: 1/4)__ Define a function `rev4` that reverses 4-tuples.
Then, prove that applying `rev4` twice is the identity function.
-/

def rev4: Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat
  | (a, b, c, d) => (d, c, b, a)

example : rev4 (1,2,3,4) = (4,3,2,1) := by rfl

theorem rev4_rev4_equiv_id4 : ∀ t : Nat × Nat × Nat × Nat, rev4 (rev4 t) = t := by
  intro t
  rfl

/-
We can use pattern matching also on nested pairs. As usual, the wildcard `_` can match everything.

For example, we define a function that takes a pair made of two pairs, and returns the sum of all elements.
-/

def addTwoPairs : (Nat × Nat) × (Nat × Nat) → Nat
  | ((a, b), (c, d)) => a + b + c + d

example : addTwoPairs ((1, 2), (3, 4)) = 10 := by rfl


/- __Exercise (difficulty: 1/4)__ Define a function that takes as input a pair `((n,m),b)`, where
`b : Bool` and `n m : Nat`, and returns the minimum of `n` and `m` if `b = false`, otherwise the maximum.
-/

def minOrMax : (Nat × Nat) × Bool → Nat
  | ((n, m), b) => if b then max n m else min n m

example : minOrMax ((1, 2), false) = 1 := by rfl
example : minOrMax ((3, 2), false) = 2 := by rfl
example : minOrMax ((1, 3), true)  = 3 := by rfl
example : minOrMax ((4, 2), true)  = 4 := by rfl

end Tuples



section Functions_returning_pairs

/-
### Functions returning pairs

A function may return several results packaged as a pair. The function below
applies two computations to the same input and returns both results.
-/

def bothResultsN (f g : Nat → Nat) (n : Nat) : Nat × Nat :=
  (f n, g n)

example : bothResultsN Nat.succ (Nat.pred) 2 = (3, 1) := rfl
example : bothResultsN Nat.succ (fun n => n+n) 5 = (6, 10) := by rfl

/- __Exercise (difficulty: 1/4)__ Define a function `minMax` that takes as input two numbers,
and returns a pair where the left element is the smaller input and right element if the the larger input. -/

def minMax (a b : Nat) : Nat × Nat :=
  (min a b, max a b)

example : minMax 3 8 = (3, 8) := by rfl
example : minMax 8 3 = (3, 8) := by rfl
example : minMax 4 4 = (4, 4) := by rfl

end Functions_returning_pairs



section Unit_type

/-
A pair contains two components, and a larger tuple contains more components.
A tuple with zero components is represented by type `Unit`.

The type `Unit` has exactly one constructor and one value:

    () : Unit

There is no information to choose when constructing `()`. This makes `Unit`
useful when a branch of a datatype needs to carry no additional data.
-/

def emptyTuple : Unit := ()


/- __Exercise (difficulty: 1/4)__ Prove that type `Unit` is inhabited. -/

theorem unit_inhabited : ∃ x : Unit, x = () := by
    simp

/- __Exercise (difficulty: 1/4)__ Prove that two elements of type `Unit` must be identical.
Hint: by case analysis. -/

theorem unit_unique (x y : Unit) : x = y := by
  cases x with
  | unit => rfl

/-
__Exercise (difficulty: 1/4)__ Show that pairing a number with `()` adds no information.
Split the proof in 3 parts:
1. Define a function `removeUnitRight : Nat × Unit → Nat`
2. Define a function `addUnitRight : Nat → Nat × Unit`
3. Prove that the composition of the two functions is the identity.
-/

def removeUnitRight (p : Nat × Unit) : Nat :=
  p.1

def addUnitRight (n : Nat) : Nat × Unit :=
  (n, ())

theorem remove_comp_add_id (n : Nat): removeUnitRight (addUnitRight n) = n := by
    rw [addUnitRight]
    rw [removeUnitRight]

theorem add_comp_remove_id (p : Nat × Unit): addUnitRight (removeUnitRight p) = p := by
    rw [removeUnitRight]
    rw [addUnitRight]


end Unit_type



section Proofs_about_products

/-
Given two elements `a`, `b`, we show that the pair `(a,b)` is equivalent to the pair of projections:
-/

theorem pair_projections (a : Nat) (b : Bool) :
    ((a, b).1, (a, b).2) = (a, b) := by
  rfl

/-
The product type `A × B` has exactly one constructor:

    Prod.mk : A → B → A × B

The pair notation `(a, b)` is shorthand for `Prod.mk a b`.

Therefore, every value of type `A × B` has the same form: a pair made of a first and a second component.

Consequently, pattern matching does not need to distinguish between different constructors;
it only extracts these two components. Consequently, one branch is sufficient:

    match p with
    | (a, b) => ...

This differs from `Bool` or `Nat` types, which have multiple constructors and
therefore require multiple branches.
-/

/-
Given a pair `p`, we show that it is equivalent to the pair of its projections.
This property is useful when a proof decomposes a pair and later reconstructs it.
-/

theorem pair_eta_NatBool (p : Nat × Bool) : (p.1, p.2) = p := by
    cases p with
    | mk a b =>
    rfl

/-
The tactic `cases` exposes how a value was constructed. For pairs, however,
writing the constructor name `mk` and a separate case branch is somewhat verbose.

The tactic `rcases` combines case analysis with a **destructuring pattern**.
The pattern

    ⟨a, b⟩

describes a pair and gives the names `a` and `b` to its two components.
Therefore,

    rcases p with ⟨a, b⟩

decomposes `p` directly into its components.
-/

theorem pair_eta_NatBool₂ (p : Nat × Bool) : (p.1, p.2) = p := by
    rcases p with ⟨a,b⟩
    rfl

/-
We now prove that `swapNatBool` is injective. More than the theorem itself, it is
interesting how we prove it. Check the proof step-by-step in the InfoView.
-/

theorem swapNatBool_inj (p1 p2 : Nat × Bool) : swapNatBool p1 = swapNatBool p2 → p1 = p2 := by
  intro h                       -- moves the antecedent of the implication to the context
  cases h1 : p1 with            -- destructs `p1`, naming the new hypothesis in the context `h1`
  | mk a1 b1 =>                 -- every value of a product type is a pair, constructed with `mk`
    cases h2 : p2 with          -- the same for `p2`
    | mk a2 b2 =>
      simp [swapNatBool,h1,h2] at h
      cases h with              -- the new `h` is a conjunction. Since a conjunction is constructed
                                -- with `And.intro`, the `cases` tactic destructs it with `intro`
      | intro c1 c2 =>          -- `c1` and `c2` are the names of the two conjuncts
        rw [c1,c2]              -- we close the proof by rewriting them in the goal.


/- Using `rcases` allows for a more concise proof. -/

theorem swapNatBool_inj₂ (p1 p2 : Nat × Bool) : swapNatBool p1 = swapNatBool p2 → p1 = p2 := by
  intro h
  rcases p1 with ⟨n1, b1⟩
  rcases p2 with ⟨n2, b2⟩
  -- The hypothesis becomes `(b1, n1) = (b2, n2)`.
  simp [swapNatBool] at h
  rcases h with ⟨n12,b12⟩
  rw [n12,b12]

end Proofs_about_products



section Type_isomorphisms

/-
## Different representations of the same information

Two types `A`, `B` may be equivalent despite being syntactically different.
We prove this equivalence by defining:

1. a transformation f from A to B;
2. a transformation g from B to A;
3. two theorems showing that f ∘ g = id and g ∘ f = id.

Such a pair of mutually inverse conversions is called a **type isomorphism**.
We write `A ≅ B` when type isomorphism holds.

Note that in the above section about the `Unit` type we have established:

    Nat × Unit  ≅  Nat.

Note that the above isomorphism holds for any type, not only `Nat`: namely, A × Unit ≅ A
holds for any type A. We postpone this generalization until we have introduced polymorphism.

For product types, we prove a sort of commutativity property:

    Nat × Bool  ≅  Bool × Nat.

We already have one direction of the transformation:

    swapNatBool : Nat × Bool → Bool × Nat.

Here is the reverse conversion.
-/

def swapBoolNat : Bool × Nat → Nat × Bool
  | (b, n) => (n, b)

/- __Exercise (difficulty: 1/4)__ Prove both round trips. -/

theorem swapBoolNat_comp_swapNatBool_id (p : Nat × Bool) : swapBoolNat (swapNatBool p) = p := by
  rfl

theorem swapNatBool_comp_swapBoolNat_id (p : Bool × Nat) : swapNatBool (swapBoolNat p) = p := by
  rfl

end Type_isomorphisms



section Currying

/-
## Curried and uncurried functions

Recall that arrows associate to the right:

    Nat → Nat → Nat

means:

    Nat → (Nat → Nat).

A function of this type receives two arguments one at a time. It is called **curried**.
In contrast,

    Nat × Nat → Nat

means:

    (Nat × Nat) → Nat.

This function receives one argument, which is a pair. It is called **uncurried**.

For example:
-/

#check (fun (n m : Nat) => n + m)           -- Nat → Nat → Nat
#check (fun ((n,m) : Nat × Nat) => n + m)   -- Nat × Nat → Nat

/-
We prove that:

    Nat × Nat → Nat ≅  Nat → Nat → Nat.

To show this type isomorphism, we define two transformations:

* `curryN` receives `a` and `b` separately, and passes the pair `(a, b)` to `f`.
* `uncurryN` matches on its pair argument and passes the two components separately to `f`.
-/

def curryN (f : Nat × Nat → Nat) : Nat → Nat → Nat :=
  fun a b => f (a, b)

def uncurryN (f : Nat → Nat → Nat) : Nat × Nat → Nat
  | (a, b) => f a b

example : curryN   (fun ((n,m) : Nat × Nat ) => n + m)  3 4   = 7 := by rfl
example : uncurryN (fun (n m : Nat) => n + m)          (3, 4) = 7 := by rfl


/- __Exercise (difficulty: 1/4)__ Prove the type isomorphism. -/

theorem curryN_uncurryN (f : Nat → Nat → Nat) : curryN (uncurryN f) = f := by
  rfl

theorem uncurryN_curryN (f : Nat × Nat → Nat) : uncurryN (curryN f) = f := by
  rfl

end Currying



section Structures

/-
Nested tuples are convenient when there are only a few components. With many
components, expressions such as `p.2.1` become difficult to read because we
must remember what every position means.

A `structure` is a product-like type whose components have names. Consider a point in the plane:
-/

structure Point where
  x : Nat
  y : Nat
  deriving Repr

/-
A structure value is constructed by giving a value for each field.
-/

def origin : Point :=
  { x := 0
    y := 0 }

def pointA : Point :=
  { x := 3
    y := 5 }

/-
Fields are accessed by name rather than by position:
-/

example : pointA.x = 3 := by rfl
example : pointA.y = 5 := by rfl

/-
Pattern matching is also available. This form makes it explicit that a
structure has one constructor carrying all its fields.
-/

def getX : Point → Nat
  | { x, y := _ } => x

def getY : Point → Nat
  | { x := _, y } => y

/-
Lean reports a warning for `y` because the pattern binds both fields of the
structure, but the body uses only `x`. This is not an error: the definition is
valid, but Lean warns us that the name `y` is unnecessary.

To remove the warning, use the pattern `{ x, y := _ }`
-/

example : pointA.x = getX pointA := by rfl

/-
Record-update syntax constructs a new value that differs in selected fields:
-/

def moveRight (p : Point) (dx : Nat) : Point :=
  { x := p.x + dx, y := p.y }

example : moveRight  pointA 1 = { x:=4, y:=5 } := by rfl

/-
Lean values are immutable: we do not modify an existing structure value. The notation:

    { p with x := newX }

constructs a new value by copying all the fields of `p`, except that field `x` is replaced by `newX`.

We can use this feature to define `moveRight` more elegantly:
-/

def moveRight₂ (p : Point) (dx : Nat) : Point :=
  { p with x := p.x + dx }

example : moveRight₂ pointA 1 = { x:=4, y:=5 } := by rfl

/-
The `y` field of the resulting point is copied automatically from `p`.
Several fields can be replaced in the same expression:

    { p with x := newX, y := newY }
-/

/-
Functions may be associated with the structure's namespace.
Dot notation then lets the input value appear before the function name:
-/

def Point.translate (p : Point) (dx dy : Nat) : Point :=
  { x := p.x + dx
    y := p.y + dy }

example : Point.translate origin 3 5 = pointA := by rfl

end Structures


end Product_types




section Sum_types

/-
## Sum types

A product contains both of its components. A **sum type** represents a choice between two alternatives.

If `A` and `B` are types, then `A ⊕ B` (type `\oplus` for `⊕`) contains either:

* a value of type `A`, introduced by `Sum.inl`;
* a value of type `B`, introduced by `Sum.inr`.

The constructor records not only the payload but also which alternative was chosen.
-/

def oneLeft   : Nat ⊕ Bool := Sum.inl 1
def trueRight : Nat ⊕ Bool := Sum.inr true

/-
The type annotation is necessary. From `Sum.inl 1` alone, Lean can infer the left type `Nat`,
but without the type annotation there would not be enough information from which to infer the right type.

We can omit the `Sum` prefix and use just `.inl` and `.inr`.
-/

def oneLeft₂   : Nat ⊕ Bool := .inl 1
def trueRight₂ : Nat ⊕ Bool := .inr true

/-
Even when the payload types coincide, the constructor tags remain distinct:
-/

def oneLeft₃  : Nat ⊕ Nat := .inl 1
def oneRight₃ : Nat ⊕ Nat := .inr 1

/- Note that the value on the left is not equal to the same value on the right.
This is because although these values carry the same number, they represent different alternatives.
-/

example : oneLeft₃ ≠ oneRight₃ := by
  intro h
  cases h


section Pattern_matching

/-
A sum has two constructors, so a function consuming a sum normally needs two branches.

For example, `natOrBoolToNat` takes as input a sum between a `Nat` or a `Bool`, and returns a `Nat`.
* In the `.inl` branch, the payload has type `Nat`.
* In the `.inr` branch, it has type `Bool`.
Every branch must return the declared result type, here `Nat`.
-/

def natOrBoolToNat : Nat ⊕ Bool → Nat
  | .inl n => n
  | .inr b => if b then 1 else 0

example : natOrBoolToNat (.inl 3)     = 3 := by rfl
example : natOrBoolToNat (.inr true)  = 1 := by rfl
example : natOrBoolToNat (.inr false) = 0 := by rfl


/- __Exercise (difficulty: 1/4)__ `isNatAlternative` tests which side was chosen. -/

def isNatAlternative : Nat ⊕ Bool → Bool
  | .inl _ => true
  | .inr b => b

example : isNatAlternative (.inl 3) = true      := by rfl
example : isNatAlternative (.inr false) = false := by rfl


/- __Exercise (difficulty: 1/4)__ Return the successor of the payload or its negation. -/

def succOrNot : Nat ⊕ Bool → Nat ⊕ Bool
  | .inl n => .inl (n + 1)
  | .inr b => .inr !b

example : succOrNot (.inl 5) = .inl 6         := by rfl
example : succOrNot (.inr true) = .inr false  := by rfl


end Pattern_matching

section Proofs_about_sums

/-
The sum type `Nat ⊕ Bool` has two constructors:

    Sum.inl : Nat  → Nat ⊕ Bool
    Sum.inr : Bool → Nat ⊕ Bool

The following functions inspect which constructor was used, without inspecting
the value stored by that constructor.
-/

def isLeft : Nat ⊕ Bool → Bool
  | .inl _ => true
  | .inr _ => false

def isRight : Nat ⊕ Bool → Bool
  | .inl _ => false
  | .inr _ => true

example : isLeft (.inl 3) = true := by rfl
example : isLeft (.inr false) = false := by rfl

/-
For every sum value, `isLeft` returns the negation of `isRight`.

Lean cannot prove this immediately by computation because `s` is arbitrary:
it does not yet know which constructor produced it. The tactic `cases s`
considers the two possible constructors separately.
-/

theorem isLeft_not_isRight (s : Nat ⊕ Bool) : isLeft s = !(isRight s) := by
  cases s with
  | inl n =>              -- `s` has the form `.inl n`
    rw [isLeft,isRight]   -- rw is not necessary! It is here just to let you observe the InfoView
    rfl
  | inr b =>              -- `s` has the form `.inr b`
    rfl

/-
The same proof can be written more compactly with `rcases`.

For a sum, the pattern

    n | b

describes its two alternatives. The tactic creates two goale:
one goal with `n : Nat`, and another goal with `b : Bool`.
-/

theorem isLeft_not_isRight₂ (s : Nat ⊕ Bool) : isLeft s = !(isRight s) := by
  rcases s with n | b
  · -- Case `s = .inl n`
    rfl
  · -- Case `s = .inr b`
    rfl

/-
The tactic `rcases` can combine product and sum patterns.

For example, consider a value `p` with type

    Nat × (Bool ⊕ Nat)

We can deconstruct `p` as follows:

  rcases p with ⟨n, b | m⟩

* `⟨n, ...⟩` decomposes the outer product;
* `b | m` considers the two constructors of the inner sum.

Consequently, `rcases` creates two goals.
-/

example (p : Nat × (Bool ⊕ Nat)) : Nat × Bool := by
  rcases p with ⟨n, b | m⟩
  · -- Here `p` had the form `(n, .inl b)`.
    exact (n, b)
  · -- Here `p` had the form `(n, .inr m)`.
    exact (m, false)


end Proofs_about_sums

section Type_isomorphisms

/-
As with products, the type operator is commutative up-to isomorphism. In particular, we prove that:

    Nat ⊕ Bool  ≅  Bool ⊕ Nat
-/

def swapNatBoolSum : Nat ⊕ Bool → Bool ⊕ Nat
  | .inl n => .inr n
  | .inr b => .inl b

def swapBoolNatSum : Bool ⊕ Nat → Nat ⊕ Bool
  | .inl b => .inr b
  | .inr n => .inl n

example : swapNatBoolSum (.inl 4) = .inr 4 := by rfl
example : swapNatBoolSum (.inr true) = .inl true := by rfl

/- __Exercise (difficulty: 1/4)__ Prove the type isomorphism:

    Nat ⊕ Bool  ≅  Bool ⊕ Nat.

Use the `cases` tactic to create two goals.
-/

theorem swapBoolNatSum_comp_swapNatBoolSum_id (s : Nat ⊕ Bool) :
    swapBoolNatSum (swapNatBoolSum s) = s := by
  cases s with
  | inl => rfl
  | inr => rfl

theorem swapNatBoolSum_comp_swapBoolNatSum_id (s : Bool ⊕ Nat) :
    swapNatBoolSum (swapBoolNatSum s) = s := by
  cases s with
  | inl => rfl
  | inr => rfl


end Type_isomorphisms



section Partial_functions

/-
Some functions may not be defined for all possible inputs. For example:
* `0` has no predecessor in `Nat`;
* division by zero is not defined;
* a requested withdrawal may exceed a balance.

We can formalize such _partial_ functions in different ways:

1. Return a "dummy" value when the function is undefined.
2. Restrict the domain to make the function total (using *dependent types*)
3. Add a special value in the codomain to represent the "undefined" value.

In this section we consider the last alternative.

Note that sum types allow us to encode the error value using `… ⊕ Unit`.

For example, we use them to define a predecessor function that is undefined on `0`:
-/

def partial_pred : Nat → Nat ⊕ Unit
  | 0     => .inr ()
  | n + 1 => .inl n

example : partial_pred 0 = .inr () := by rfl
example : partial_pred 3 = .inl 2  := by rfl


/-
__Exercise (difficulty: 1/4)__: Define a function that takes an even number as input and returns
the next even number. If the input is not an even number, then the function is undefined.
Hint: use the modulus operator: `%`.
-/

def nextEven (n : Nat): Nat ⊕ Unit :=
    if n % 2 == 0 then .inl (n + 2) else .inr ()

example : nextEven 4 = .inl 6  := by rfl
example : nextEven 5 = .inr () := by rfl

/-
We define a function that takes two partial functions and sums them.
The sum is undefined when any of the inputs is undefined.
-/

def partial_sum (f g: Nat → Nat ⊕ Unit) (n : Nat) : Nat ⊕ Unit :=
  match f n with
  | .inr () => .inr ()
  | .inl rf => match g n with
    | .inr () => .inr ()
    | .inl rg => .inl (rf + rg)


example : (partial_sum partial_pred nextEven) 0 = .inr () := by rfl
example : (partial_sum partial_pred nextEven) 1 = .inr () := by rfl
example : (partial_sum partial_pred nextEven) 2 = .inl 5  := by rfl

/-
Lean features a special type constructor `Option` to deal with partial functions.
For example, the type `Option Nat` has two forms:

    none   : Option Nat   --- the "undefined value"
    some n : Option Nat   --- the tagged payload when the function is defined

`Option` itself works with any payload types, not just `Nat` (see next lecture on polymorphism).
-/

def partial_pred₂ : Nat → Option Nat
  | 0     => none
  | n + 1 => some n

example : partial_pred₂ 0 = none := by rfl
example : partial_pred₂ 3 = some 2  := by rfl

/-
When a function calls another function that returns an Option value,
the caller must inspect a result before using the possible number.
-/

def getOrElseN (default : Nat) : Option Nat → Nat
  | none   => default
  | some n => n

example : getOrElseN 100 (partial_pred₂ 8) = 7 := by rfl
example : getOrElseN 100 (partial_pred₂ 0) = 100 := by rfl


/- __Exercise (difficulty: 1/4)__ Define partial subtraction.
It returns `none` instead of truncating to zero when `b > a`. -/

def partial_sub (a b : Nat) : Option Nat :=
  if b > a then none else some (a - b)

example : partial_sub 10 3 = some 7 := by rfl
example : partial_sub 3 10 = none   := by rfl

/- __Exercise (difficulty: 1/4)__ Add two optional numbers only when both are present. -/

def partial_sum₂ (f g: Nat → Option Nat) (n : Nat) : Option Nat :=
  let part := (f n, g n)
  match part with
  | (some a, some b) => some (a + b)
  | (_, _) => none

example : (partial_sum₂ partial_pred₂ (partial_sub 10)) 0  = none   := by rfl
example : (partial_sum₂ partial_pred₂ (partial_sub 10)) 11 = none   := by rfl
example : (partial_sum₂ partial_pred₂ (partial_sub 10)) 2  = some 9 := by rfl

end Partial_functions


section Proofs_about_sums

/-
The sum type `A ⊕ B` has two constructors:

    Sum.inl : A → A ⊕ B
    Sum.inr : B → A ⊕ B

Consequently, pattern matching needs to distinguish between different constructors:

    match s with
    | .inl a => ...
    | .inr b => ...

This differs from product types, which have a single constructor.
-/

/-
We now prove that `partial_sum` is commutative. More than the theorem itself, it is
interesting how we prove it. Check the proof step-by-step in the InfoView.
-/

theorem partial_sum_comm (f1 f2: Nat → Nat ⊕ Unit) (n : Nat) : partial_sum f1 f2 n = partial_sum f2 f1 n := by
  cases h1 : f1 n with
  | inl r1 =>
    cases h2 : f2 n with
    | inl r2 =>
      simp [partial_sum, h1, h2]
      rw [Nat.add_comm]
    | inr _ =>
      simp [partial_sum, h1, h2]
  | inr _ =>
    cases h2 : f2 n with
    | _ => simp [partial_sum, h1, h2]


end Proofs_about_sums


end Sum_types



section Exercises


section Domain_restriction

/-
## Exercise: Domain restriction

**Difficulty: 2/4**

Write a function `restrict` that takes as input a function `f` and a predicate `p`, and returns
a function `g` that behaves as `f` on the input values that satisfy `p`, and is undefined otherwise.

  restrict : (Nat → Nat) → (Nat → Bool) → Nat → Option Nat
-/

def restrict (f : Nat → Nat) (p : Nat → Bool) : (Nat → Option Nat) :=
  fun x => if p x then some (f x) else none

def f1_res := restrict Nat.succ (fun x => x>0)
example : f1_res 1 = some 2 := by rfl
example : f1_res 0 = none   := by rfl

/- Prove that `restrict f p n` is undefined whenever `p n` is false. -/

theorem restrict_none (f : Nat → Nat) (p : Nat → Bool) :
  ∀ n : Nat, p n = false → restrict f p n = none := by
    intro n
    intro h
    unfold restrict
    simp
    exact h

/- Prove that `restrict f p n` is defined whenever `p n` is true. -/

theorem restrict_some (f : Nat → Nat) (p : Nat → Bool) :
  ∀ n : Nat, p n = true → exists v : Nat, restrict f p n = some v := by
    intro n
    intro h
    unfold restrict
    simp
    exact h

end Domain_restriction



section Max_option

/- ## Exercise: Partial maximum

**Difficulty: 1-3/4**
-/

/- __Exercise (difficulty: 1/4)__ Define partial maximum. -/

def max_option (o1 o2: Option Nat) : Option Nat :=
  max o1 o2

example : max_option (some 3) (some 5) = some 5 := by rfl
example : max_option (some 3) none = some 3     := by rfl
example : max_option none (some 5) = some 5     := by rfl


/- __Exercise (difficulty: 3/4)__ Prove that partial maximum is undefined whenever both inputs are none. -/

theorem max_option_none (o1 o2: Option Nat) : max_option o1 o2 = none ↔ o1 = none ∧ o2 = none := by
    simp [max_option]

/-
__Exercise (difficulty: 3/4)__ Prove the following property of the partial maximum.
Follow the skeleton of the proof, inspecting the InfoView, and resolve the sorries.
-/

theorem max_option_preserves_lower_bound
    (a lower : Nat) (b : Option Nat) (ha : lower ≤ a) :
    ∃ c, max_option (some a) b = some c ∧ lower ≤ c := by
    simp [max_option]
    cases b with
    | none =>
        simp
        exact ha
    | some k =>
        simp
        omega

end Max_option



section Arithmetic_expressions

/- ## Exercise: arithmetic expressions

**Difficulty: 2/4**

Consider the following type to define simple arithmetic expressions: -/

inductive Aexp where
  | val : Nat → Aexp
  | add : Aexp × Aexp → Aexp
  | sub : Aexp × Aexp → Aexp
  | mul : Aexp × Aexp → Aexp
  | div : Aexp × Aexp → Aexp

/-
Write a function:

  eval : Aexp → Option Nat

that evaluates the expression, in a big-step style.

Evaluation is a partial function. It is undefined in the following cases:
* a division by zero;
* a subtraction `n1 - n2` where `n2 > n1`.
-/

def eval (e : Aexp) : Option Nat :=
  match e with
  | .val n => some n
  | .add (e1, e2) =>
    match eval e1, eval e2 with
    | some n, some m => some (n + m)
    | _, _ => none
  | .sub (e1, e2) =>
    match eval e1, eval e2 with
    | some n, some m => if m > n then none else some (n - m)
    | _, _ => none
  | .mul (e1, e2) =>
    match eval e1, eval e2 with
    | some n, some m => some (n * m)
    | _, _ => none
  | .div (e1, e2) =>
    match eval e1, eval e2 with
    | some n, some m => if m == 0 then none else some (n / m)
    | _, _ => none

example : eval (Aexp.add (Aexp.val 1, Aexp.val 2)) = some 3                      := by rfl
example : eval (Aexp.add (Aexp.val 1, Aexp.sub (Aexp.val 2, Aexp.val 3))) = none := by rfl
example : eval (Aexp.mul (Aexp.val 1, Aexp.div (Aexp.val 2, Aexp.val 0))) = none := by rfl


/-
__Exercise (difficulty: 2/4)__ Prove the following properties of evaluation and addition:
* `eval_add_success`: if both operands evaluate successfully, their addition also evaluates successfully;
* `eval_add_error_left`: if the evaluation of the first operand fails, then the evaluation of addition fails;
* `eval_add_error_right`: if the evaluation of the second operand fails, then the evaluation of addition fails;
* `eval_add_zero_right`: adding zero does not change the result of evaluation, even when evaluation fails;
* `eval_add_commutative`: addition is commutative;
* `eval_add_characterization`: an addition evaluates to `n` iff its operands evaluate to two numbers whose sum is `n`;
* `eval_add_associative`: addition is associative.
-/

theorem eval_add_success
    (e1 e2 : Aexp) (n1 n2 : Nat)
    (h1 : eval e1 = some n1)
    (h2 : eval e2 = some n2) :
    eval (.add (e1, e2)) = some (n1 + n2) := by
    simp [eval]
    rw [h1, h2]

theorem eval_add_error_left
    (e1 e2 : Aexp)
    (h : eval e1 = none) :
    eval (.add (e1, e2)) = none := by
    simp [eval]
    rw [h]

theorem eval_add_error_right
    (e1 e2 : Aexp)
    (h : eval e2 = none) :
    eval (.add (e1, e2)) = none := by
    simp [eval]
    rw [h]
    simp

theorem eval_add_zero_right (e : Aexp) :
    eval (.add (e, .val 0)) = eval e := by
    cases k: eval e with
    | none =>
        unfold eval
        rw [k]
    | some n =>
        unfold eval
        rw [k]
        simp [eval]

theorem eval_add_commutative (e1 e2 : Aexp) :
    eval (.add (e1, e2)) = eval (.add (e2, e1)) := by
    cases h1 : eval e1 with
    | none =>
        cases h2 : eval e2 with
        | none => simp [eval, h1, h2]
        | some => simp [eval, h1, h2]
    | some n =>
        cases h2 : eval e2 with
        | none => simp [eval, h1, h2]
        | some m => simp [eval, h1, h2, Nat.add_comm]

theorem eval_add_characterization
    (e1 e2 : Aexp) (n : Nat) :
    eval (.add (e1, e2)) = some n ↔
      ∃ n1 n2,
        eval e1 = some n1 ∧
        eval e2 = some n2 ∧
        n = n1 + n2 := by
    cases h1 : eval e1 with
    | none =>
        cases h2 : eval e2 with
        | none => simp [eval, h1, h2]
        | some => simp [eval, h1, h2]
    | some n =>
        cases h2 : eval e2 with
        | none => simp [eval, h1, h2]
        | some m =>
            simp [eval]
            rw [h1, h2]
            simp
            omega

theorem eval_add_associative (e1 e2 e3 : Aexp) :
    eval (.add ((.add (e1, e2)), e3)) = eval (.add (e1, (.add (e2,e3)))) := by
    simp [eval]
    cases h: eval e1 with
    | none =>
        simp
    | some n =>
        cases h3: eval e3 with
        | none => simp
        | some m =>
            cases h2: eval e2 with
            | none => rfl
            | some k =>
                simp
                omega


end Arithmetic_expressions



section Students_grades

/- ## Exercise: Students' grades

Consider the following type to represent a student's grades in an exam: -/

structure Grade where
  name    : String        -- the student's name
  written : Option Nat    -- the grade of the written part
  oral    : Option Nat    -- the grade of the oral part
  deriving Repr

/-
__Exercise (difficulty: 1/4)__ Define a function that returns the sum of the written and oral grades.
-/

def opt_sum : (Option Nat × Option Nat) → Option Nat
    | (some a, some b) => some (a + b)
    | (_, _) => none

def total_score : Grade -> Option Nat
    | { name := _, written, oral } =>  opt_sum (written, oral)

def mario : Grade := { name := "Mario", written := some 18, oral := some 15 }
def luigi : Grade := { name := "Luigi", written := some 15, oral := none }
def alice : Grade := { name := "Alice", written := some 28, oral := some 30 }

example : total_score mario = some 33 := by rfl
example : total_score luigi = none    := by rfl
example : total_score alice = some 58 := by rfl

/-
__Exercise (difficulty: 1/4)__ Prove that `total_score` does not depend on the student's name.
-/

example (g : Grade) (newName : String) :
    total_score { g with name := newName } = total_score g := by
  rfl

/-
__Exercise (difficulty: 3/4)__ Study the following characterization of `total_score`.
Follow the skeleton of the proof, inspecting the InfoView, and resolve the sorries.
-/

theorem total_score_characterization (g : Grade) (score : Nat) :
    total_score g = some score ↔
      ∃ w o,
        g.written = some w ∧
        g.oral = some o ∧
        score = w + o := by

  simp [total_score, opt_sum]
  cases g with
  | mk s w o =>
    simp
    cases w with
    | none => cases o with
      | none => simp
      | some k => simp
    | some n => cases o with
      | none => simp
      | some k =>
      simp
      omega

/-
__Exercise (difficulty: 1/4)__ Define a function that returns true if both grades are at least 18, and false otherwise.
-/

def passed (g : Grade) : Bool :=
    match g with
    | { name := _, written, oral } => match (written, oral) with
        | (some w, some o) => w >= 18 && o >= 18
        | (_, _) => false

example : passed mario = false := by rfl
example : passed luigi = false := by rfl
example : passed alice = true  := by rfl

example (g : Grade) (newName : String) :
    passed { g with name := newName } = passed g := by
  rfl

/-
__Exercise (difficulty: 2/4)__ Study the following property of `passed`.
Try to write in English what this property actually states.
Experiment with LLMs to construct a proof.
Is the converse implication true? If not, prove it.
-/

theorem passed_implies_minimum_total (g : Grade) :
    passed g = true →
      ∃ score : Nat,
        total_score g = some score ∧ score ≥ 36 := by
    intro h
    cases g with
    | mk _ w o =>
        cases w with
        | none => cases o with
            | none =>
                simp [total_score, opt_sum]
                cases h
            | some n =>
                simp [total_score, opt_sum]
                cases h
        | some n => cases o with
            | none =>
                simp [total_score, opt_sum]
                cases h
            | some m =>
                simp [total_score, opt_sum]
                rw [passed] at h
                simp at h
                omega
/-
__Exercise (difficulty: 2/4)__ Define a function that, given two results of the same student,
returns a new result with the maximum grades between the two results.
The function is partial: if the names of the two students do not match, then it is undefined.

Hint: use `max_option`
-/

def max_grade (g1 g2: Grade) : Option Grade :=
    if g1.name = g2.name then
        some { g1 with oral := max_option g1.oral g2.oral, written := max_option g1.written g2.written }
    else none

example : max_grade mario luigi = none := by rfl

def luigi2 : Grade := { name := "Luigi", written := some 12, oral := some 17 }
def alice2 : Grade := { name := "Alice", written := some 30, oral := none }

example : max_grade luigi luigi2 = some { name := "Luigi", written := some 15, oral := some 17 } := by rfl
example : max_grade alice alice2 = some { name := "Alice", written := some 30, oral := some 30 } := by rfl

/-
__Exercise (difficulty: 3/4)__ Study the following property of `max_grade`.
Try to write in English what this property actually states.
Experiment with LLMs to construct a proof.
Is the converse implication true? If not, prove it.
-/

theorem max_grade_passed (g1 g2 g12: Grade) (h: max_grade g1 g2 = some g12) :
    passed g1 = true → passed g12 = true := by
    intro h2
    cases g1 with
    | mk n1 w1 o1 =>
        cases g2 with
        | mk n2 w2 o2 =>
        simp [max_grade] at h
        cases w1 with
        | none => cases h2
        | some a =>
        cases o1 with
        | none => cases h2
        | some b =>
          simp [passed] at h2
          rcases h2 with ⟨h2a, h2b⟩
          rcases max_option_preserves_lower_bound a 18 w2 h2a with ⟨c1, hc1, hc1'⟩
          rcases max_option_preserves_lower_bound b 18 o2 h2b with ⟨c2, hc2, hc2'⟩
          rcases h with ⟨hn, h⟩
          rw [← h, hc1, hc2]
          simp [passed]
          omega


end Students_grades



section Type_reconstructions

/- __Exercise (difficulty: 1-2/4)__ Define functions respecting the types.
There are many correct answers: some of them are trivial, but also look for non-trivial ones.
-/

example : (Nat × Nat) → (Nat × Nat)
    | (a, b) => (a + 1, b + 2)

example : Nat → (Nat × Nat) → Nat
    | a, (b, c) => a + b + c

example : Nat → (Nat × Nat) → (Nat × Nat)
    | a, (b, c) => (a + b, a * c)

example : (Nat × Nat) → Nat → (Nat × Nat)
    | (a, b), c => (a * b, b + c)

example : (Nat × Nat) → (Nat × Nat) → Nat
    | (a, b), (c, d) => a + b + c + d

example : (Nat × Bool) → (Nat ⊕ Bool)
    | (n, b) => if b then (.inl n) else (.inr b)

example : Nat → Bool → Bool → (Nat ⊕ Bool)
  | a, b, c => if b && c then (.inl (a + 1)) else (.inr false)

example : (Nat ⊕ Bool) → (Nat ⊕ Bool) → (Nat ⊕ Bool)
  | a, b => match a with
    | .inl n => match b with
      | .inr m => if m then .inr false else .inl (n + 1)
      | _ => .inr true
    | _ => .inl 0

example : (Nat → String) ⊕ (String × Bool) → Nat → String
  | a, n => match a with
    | .inl fn => fn n
    | .inr (s, b) => if b then s else s.append s

example : (Nat → String) ⊕ (Bool → String) → (Nat × Bool) → String
  | a, (n, b) => match a with
    | .inl fn => fn n
    | .inr fn => fn b

end Type_reconstructions



section Type_isomorphisms

/- In this section we prove a few type isomorphisms. -/

/-
## Exercise: Point and Nat × Nat (difficulty: 1/4)

Prove that types `Point` and `Nat × Nat` are isomorphic:

    Point  ≅  Nat × Nat
-/

def pointToPair (p : Point) : Nat × Nat :=
  (getX p, getY p)

def pairToPoint : Nat × Nat → Point
  | (x, y) => {x := x, y := y}

theorem point_pair_id : pairToPoint ∘ pointToPair = id := by
  funext p
  simp
  rw [pointToPair, pairToPoint]
  simp [getX, getY]

theorem pair_point_roundtrip : pointToPair ∘ pairToPoint = id := by
  funext p
  simp
  rw [pointToPair, pairToPoint]
  simp [getX, getY]


/-
## Exercise: Sums and Options (difficulty: 1/4)

Prove the type isomorphism:

    Nat ⊕ Unit  ≅  Option Nat
-/

def sumNatUnit_to_NatOption (s : Nat ⊕ Unit) : Option Nat :=
  match s with
  | .inl n => some n
  | .inr _ => none

def sumNatOption_to_NatUnit (o : Option Nat) : Nat ⊕ Unit :=
  match o with
  | none => .inr ()
  | some n => .inl n

theorem sumOption_right_left (s : Nat ⊕ Unit) :
  sumNatOption_to_NatUnit (sumNatUnit_to_NatOption s) = s := by
  simp [sumNatUnit_to_NatOption]
  simp [sumNatOption_to_NatUnit]
  cases s with
  | inl n => simp
  | inr u => simp


theorem sumOption_left_right (o : Option Nat) :
  sumNatUnit_to_NatOption (sumNatOption_to_NatUnit o) = o := by
  simp [sumNatUnit_to_NatOption]
  simp [sumNatOption_to_NatUnit]
  cases o with
  | none => simp
  | some n => simp

/-
## Exercise: Bool and Unit × Unit (difficulty: 2/4)

Prove the type isomorphism:

      Bool  ≅  Unit ⊕ Unit
-/

def boolToSum : Bool → Unit ⊕ Unit
  | true => .inl ()
  | false  => .inr ()

def sumToBool : Unit ⊕ Unit → Bool
  | .inl _ => true
  | .inr _ => false

theorem boolToSum_sumToBool_id (s : Unit ⊕ Unit) : boolToSum (sumToBool s) = s := by
  simp [sumToBool, boolToSum]
  cases s with
  | inl _ => rfl
  | inr _ => rfl

theorem sumToBool_boolToSum_id (b : Bool) : sumToBool (boolToSum b) = b := by
  simp [sumToBool, boolToSum]
  cases b with
  | true => rfl
  | false => rfl


/-
## Exercise: Associativity of products (difficulty: 1/4)

Prove the type isomorphism:

    Nat × (Bool × String)  ≅  (Nat × Bool) × String
-/

def associateProductLeft : Nat × (Bool × String) → (Nat × Bool) × String
  | (n, (b, s)) => ((n, b), s)

def associateProductRight : (Nat × Bool) × String → Nat × (Bool × String)
  | ((n, b), s) => (n, (b, s))

theorem associateProduct_right_left (p : Nat × (Bool × String)) :
  associateProductRight (associateProductLeft p) = p := by
  simp [associateProductLeft, associateProductRight]

theorem associateProduct_left_right (p : (Nat × Bool) × String) :
  associateProductLeft (associateProductRight p) = p := by
  simp [associateProductRight, associateProductLeft]


/-
## Exercise: Associativity of sums (difficulty: 2/4)

Prove the type isomorphism:

    Nat ⊕ (Bool ⊕ String)  ≅  (Nat ⊕ Bool) ⊕ String
-/

def associateSumLeft : Nat ⊕ (Bool ⊕ String) → (Nat ⊕ Bool) ⊕ String
  | .inl n => .inl (.inl n)
  | .inr sum => match sum with
    | .inl b => .inl (.inr b)
    | .inr s => .inr s

def associateSumRight : (Nat ⊕ Bool) ⊕ String → Nat ⊕ (Bool ⊕ String)
  | .inl sum => match sum with
    | .inl n => .inl n
    | .inr b => .inr (.inl b)
  | .inr s => .inr (.inr s)

theorem associateSum_right_left (s : Nat ⊕ (Bool ⊕ String)) :
    associateSumRight (associateSumLeft s) = s := by
  simp [associateSumLeft, associateSumRight]
  cases s with
  | inl n => rfl
  | inr sum => cases sum with
    | inl b => rfl
    | inr s => rfl

/-
## Exercise: Distributivity of products over sums (difficulty: 2/4)

Prove the type isomorphism:

    Nat × (Bool ⊕ Nat)  ≅  (Nat × Bool) ⊕ (Nat × Nat)

This is a concrete instance of the general distributive pattern:

    A × (B + C)  ≅  (A × B) + (A × C).
-/

def distributeNatBoolNat : Nat × (Bool ⊕ Nat) → (Nat × Bool) ⊕ (Nat × Nat)
  | (n, u) => match u with
    | .inl b => .inl (n, b)
    | .inr m => .inr (n, m)

def factorNatBoolNat : (Nat × Bool) ⊕ (Nat × Nat) → Nat × (Bool ⊕ Nat)
  | .inl (n, b) => (n, .inl b)
  | .inr (n, m) => (n, .inr m)

example : distributeNatBoolNat (3, .inl true) = .inl (3, true) := by
  rfl

example : distributeNatBoolNat (3, .inr 8) = .inr (3, 8) := by
  rfl

theorem factor_after_distribute (p : Nat × (Bool ⊕ Nat)) :
  factorNatBoolNat (distributeNatBoolNat p) = p := by
  simp [distributeNatBoolNat, factorNatBoolNat]
  cases p with
  | mk n u => cases u with
    | inl b => rfl
    | inr m => rfl

theorem distribute_after_factor (s : (Nat × Bool) ⊕ (Nat × Nat)) :
  distributeNatBoolNat (factorNatBoolNat s) = s := by
  simp [distributeNatBoolNat, factorNatBoolNat]
  cases s with
  | inl nb => cases nb with
    | mk n b => rfl
  | inr nm => cases nm with
    | mk n m => rfl


end Type_isomorphisms


end Exercises
