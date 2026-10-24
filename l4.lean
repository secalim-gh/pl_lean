/-
The following import brings into scope the definitions and theorems from the
previous lectures, including `addN`, `mulN`, `doubleN`, `isEven`, and `eqN`.

If you are working on `https://live.lean-lang.org/`, remove the import and
copy the required code from the previous lectures before this file.
-/

import pl_lean.l3


set_option autoImplicit false


/-
# Function types and higher-order functions

Until now, most of our functions consumed ordinary data such as Booleans and
natural numbers.  In this lecture we take an important functional-programming
idea seriously:

    a function is itself a value.

A function can therefore be named, passed as an argument, selected by a
conditional, or returned as the result of another function.  Functions that
consume or produce functions are called *higher-order functions*.

By the end of the lecture, you should be able to:

* read function types containing several arrows and parentheses;
* remember that arrows associate to the right and applications to the left;
* write anonymous functions with `fun`;
* use partial application;
* define functions that accept or return other functions;
* use composition and iteration to build new computations;
* prove pointwise properties and equalities between functions;
* explain the role of every argument of a higher-order function.

For the moment, our data types will remain `Bool` and `Nat`.  The only type
constructor introduced here is the function arrow `→`.

Exercise difficulties use the same relative scale as in PL03:

* **1/4:** one direct idea;
* **2/4:** two ideas must be combined;
* **3/4:** a more substantial higher-order construction;
* **4/4:** an optional challenge.
-/


section Reading_function_types

/-
## Reading simple function types

For this lecture, the types we use can be described informally by the grammar

    T ::= Bool | Nat | T₁ → T₂

Lean's type system is much richer than this.  We are deliberately working inside
this small, simply typed fragment so that we can focus on function values.

`Bool` and `Nat` are *base types*.  If `A` and `B` are types, then

    A → B

is the type of functions that accept an input of type `A` and return a result
of type `B`.  We call `A` the *domain* and `B` the *codomain*.

Two rules account for most of what happens in this lecture:

* **function creation:** if an expression `e` has type `B` while `x` has type
  `A`, then `fun x : A => e` has type `A → B`;
* **function application:** if `f : A → B` and `a : A`, then `f a : B`.

In the application rule, the argument type must match the function's domain.
The type of the whole application is the function's codomain.  Type checking
therefore prevents us from connecting incompatible computations.

-/

#check Nat.succ
#check isEven
#check addN

/-
Lean reports the following types:

    Nat.succ : Nat → Nat
    isEven   : Nat → Bool
    addN     : Nat → Nat → Nat

The first two types have one arrow:

* `Nat.succ` consumes a natural number and returns a natural number;
* `isEven` consumes a natural number and returns a Boolean.

The type of `addN` contains two arrows.  Arrows associate to the *right*, so

    Nat → Nat → Nat

means

    Nat → (Nat → Nat)

and not

    (Nat → Nat) → Nat.

Thus `addN` first consumes one `Nat`; its result is a function that consumes
the second `Nat` and finally returns a `Nat`.
-/

#check addN 5
#check (addN 5 : Nat → Nat)
#check addN 5 3

/-
Function application associates to the *left*.  Therefore

    addN 5 3

means

    (addN 5) 3.

These two conventions work together:

    arrows associate right; applications associate left.

Parentheses can radically change a type:

    Nat → Nat → Nat          a function consumes a Nat and returns a function
    (Nat → Nat) → Nat        a function that consumes a function and returns a Nat
    (Nat → Nat) → Nat → Nat  a function that consumes a function, then a Nat

The parentheses around `Nat → Nat` in the last two types cannot be omitted.
-/

/-
__Exercise__: Explain why the following commented commands would be rejected.  Do not
uncomment both at once: read one expected error at a time.

-- #check Nat.succ false
-- #check addN Nat.succ 3
-- #check addN 1 true
-/

end Reading_function_types



section Anonymous_functions

/-
## Anonymous functions

A function need not have a name.  The expression

    fun n : Nat => n + 1

is an *anonymous function*, also called a *lambda abstraction*.  It accepts a
natural number named `n` and returns `n + 1`.
-/

#check (fun n : Nat => n + 1)
#eval (fun n : Nat => n + 1) 5

/-
Function application substitutes the argument for the parameter:

    (fun n : Nat => n + 1) 5
    = 5 + 1
    = 6

The type annotation `: Nat` can be omitted, since Lean can infer the type from the context.
-/

/- Of course we can give names to functions defined anonymously -/
def incr := fun n : Nat => n + 1

/-
The following theorem states that the two functions return the same result on every input.
This is stated as a *pointwise equality*. Later we will express similar results as *function equality*.
-/
example : ∀ (n : Nat), incr n = (fun n : Nat => n + 1) n := by
  intros n
  rfl


/- __Exercise__: Resolve the sorry's. -/

example : (fun f => f 5) (fun n => n + 1) = 6 := by rfl
example : (fun f => f 5) (fun n => n * n) = 25 := by rfl


/-
An anonymous function may use variables from its surrounding context:
-/

def incrBy (k : Nat) : Nat → Nat := fun n => n + k

/-
The parameter `k : Nat` provided in the context can be equivalently moved
under the lambda-abstraction.
-/

example (k n : Nat): incrBy k n = (fun k : Nat => fun n : Nat => n + k) k n := by rfl

example : ∀ (k n : Nat), incrBy k n = (fun k : Nat => fun n : Nat => n + k) k n := by
  intros k n
  rfl

end Anonymous_functions



section Functions_as_arguments

/-
## Passing functions as arguments

Here is a more interesting example of a higher-order function: apply a given function twice.
-/

def applyTwiceN (f : Nat → Nat) (n : Nat) : Nat := f (f n)


/-
Lean prints a type equivalent to

    applyTwiceN : (Nat → Nat) → Nat → Nat

Read it from left to right, respecting the parentheses:

1. `applyTwiceN` first receives a function `f : Nat → Nat`;
2. it then receives an initial value `n : Nat`;
3. it finally returns a `Nat`.

The implementation does not know what `f` does.  It only knows that the output
of `f` is another `Nat`, so that it is legal to apply `f` again.

This is why `isEven` cannot be supplied to `applyTwiceN`: `isEven` returns a
`Bool`, but a second application would require another `Nat`.

    -- #check applyTwiceN isEven 5
-/


/- __Exercise__: Resolve the sorry's -/
example : applyTwiceN Nat.succ 5 = 7 := by rfl
example : applyTwiceN doubleN 3 = 12 := by rfl
example : applyTwiceN (fun n => n * n) 2 = 16 := by rfl
example : applyTwiceN (applyTwiceN Nat.succ) 0 = 4 := by rfl


/- __Exercise__: Define a function `applyThreeTimesN` satisfying the given tests. -/

def applyThreeTimesN (f : Nat → Nat) (n : Nat) : Nat :=
  applyTwiceN f  (f n)

example : applyThreeTimesN Nat.succ 5 = 8 := by rfl
example : applyThreeTimesN doubleN 1 = 8 := by rfl

end Functions_as_arguments



section Functions_as_return_values

/-
## Partial application and functions that return functions

Recall the type

    addN : Nat → (Nat → Nat).

We have already noted that if we supply only the first `Nat` argument,
the result is a function of type `Nat → Nat`:
-/

def addFive : Nat → Nat := addN 5

/-
Supplying fewer arguments than a function can eventually consume is called
*partial application*.  No special mechanism is involved: `addN 5` is simply
the result of the first function application.
-/

/-
Functions are ordinary values, so a conditional can select between them too.
-/

def chooseN (s : Bool) (f g : Nat → Nat) : Nat → Nat :=
  if s then f else g

/- __Exercise__: Resolve the sorry's. -/

example : chooseN true  doubleN Nat.succ 4 = 8 := by rfl
example : chooseN false doubleN Nat.succ 4 = 5 := by rfl

/-
Note that `chooseN` does not run `f` or `g`: it just chooses one of the two functions.
The chosen function is applied to `4` only afterwards.
-/


/- __Exercise__: define a function `sumFun : (Nat → Nat) → (Nat → Nat) → (Nat → Nat)`
that returns the pointwise summation of its inputs. Namely, `sumFun f g` returns a
function `h` such that `h(n) = f(n) + g(n)`, for all `n : Nat`.
-/

def sumFun (f g : Nat → Nat) : (Nat → Nat) :=
  fun x : Nat => f x + g x

example : sumFun (fun n => n+1) (fun n => n+n) 3 = 10 := by rfl
example : sumFun (fun n => n+1) (fun n => n+n) 5 = 16 := by rfl

end Functions_as_return_values



section Composition

/-
## Building functions by composition

Given two functions

    f : Nat → Nat
    g : Nat → Nat

we can build a new function that first applies `g` and then applies `f` to the result.
This operation is called *function composition*.
-/

def composeN (f g : Nat → Nat) : Nat → Nat :=
  fun n => f (g n)

/- __Exercise__: resolve the sorry's -/

example : composeN Nat.succ doubleN 3 = 7 := by rfl
example : composeN doubleN Nat.succ 3 = 8 := by rfl

/-
After solving the previous exercise, you should realise that function composition is
sensitive to order.  In `composeN f g`, the function `g` is the one applied first.

More generally, composition is well-typed when the output type of the first
computation matches the input type of the second.  For example, the function
`applyThenTest` first applies a function `f : Nat → Nat` to its argument, and then
tests it with a function `p : Nat → Bool`.
-/

def applyThenTest (p : Nat → Bool) (f : Nat → Nat) : Nat → Bool :=
  fun n => p (f n)

/- __Exercise__: resolve the sorry's -/

example : applyThenTest isEven Nat.succ 3 = true := by rfl
example : applyThenTest isEven Nat.succ 4 = false := by rfl

/-
Lean has a built-in composition operator `∘`, entered as `\comp`:
-/

example : ((fun n : Nat => n + 1) ∘ (fun n : Nat => n * 2)) 5 = 11 := by rfl


/-
### Equality between functions

To prove that two functions are equal, it is enough to prove that they return
equal results on every input.  This principle is called *function extensionality*.

We have already used this principle above, to prove that `incrBy` is equal to its anonymous version.

The `funext` tactic introduces an arbitrary input and changes a function-equality goal into a pointwise equality.
-/

def idN : Nat → Nat := fun n => n

theorem composeN_identity_left (f : Nat → Nat) : composeN idN f = f := by
  funext n
  rfl

/-
__Exercise__: prove that `idN` is also the right identity of composition.
-/

theorem composeN_identity_right (f : Nat → Nat) : composeN f idN = f := by
  rfl


/-
__Exercise__ Prove that function composition is associative.
-/

theorem composeN_assoc (f g h : Nat → Nat) :
    composeN (composeN f g) h = composeN f (composeN g h) := by
  rfl

end Composition



section State_transformers

/-
## Application: programs as state transformers

A function `Nat → Nat` can be read as a tiny program that transforms a state.
For example, suppose that the state is the balance of a bank account.  A
deposit and a withdrawal are functions from the old balance to the new one.

The returned functions remember the amount, so these are also simple examples
of closures.
-/

def deposit (amount : Nat) : Nat → Nat :=
  fun balance => balance + amount

def withdraw (amount : Nat) : Nat → Nat :=
  fun balance => balance - amount

example : deposit 20 100 = 120 := by rfl
example : withdraw 7 100 = 93  := by rfl

/-
In this context, function composition represents the sequential execution of
account operations. Recall that the function written on the right
is executed first.
-/

example : composeN (deposit 20) (withdraw 7) 5 = 20 := by rfl

example : composeN (withdraw 7) (deposit 20) 5 = 18 := by rfl

/-
This example gives a concrete reason why the order of composition matters.
It also shows why functions that represent actions are useful values: they can
be assembled into a larger program before any initial state is supplied.
-/

/-
__Exercise__: Prove that depositing zero is the identity transformation.

Hint: Use `funext` and `simp`.
-/

theorem deposit_zero : deposit 0 = idN := by
  funext n
  rfl

/-
__Exercise__: Prove that two consecutive deposits can be combined into one.

Hint: Use `funext` and `simp`.
-/

theorem deposit_additivity (a b : Nat) : composeN (deposit a) (deposit b) = deposit (b + a) := by
  funext n
  rw [composeN]
  simp [deposit]
  rw [Nat.add_assoc]
/-
__Exercise__: Prove that the effect of a deposit can be reverted by a subsequent withdraw.

Hint: Use `exists` tactic to provide a witness for the existentially quantified variable `b`.
-/

theorem deposit_reversibility : ∀ a : Nat, ∃ b : Nat, composeN (withdraw b) (deposit a) = idN := by
  intro b
  exists b
  funext n
  rw [composeN]
  rw [withdraw]
  rw [deposit]
  simp
  rfl

end State_transformers



section Iteration

/-
## Iterating a function

Composition describes a fixed sequence of operations.  Often we instead want
to repeat the same operation a number of times that is not fixed in the definition.

The function `iterateN` takes as input both the function we want to apply and the number of repetitions.

The three arguments play different roles:
* `f` describes what one step does;
* `k` describes how many steps are performed;
* `n` is the initial state.

For example:

    iterateN f 3 n = f (f (f n)).

Recursion controls *how often* something happens; the function argument says *what* happens.
-/

def iterateN (f : Nat → Nat) (k n : Nat) : Nat :=
  match k with
  | 0      => n                     -- applying a function zero times leaves the starting value unchanged
  | k' + 1 => f (iterateN f k' n)

example : iterateN Nat.succ 5 0 = 5 := by rfl

/- __Exercise__ Resolve the sorry's -/

example : iterateN Nat.succ 3 12 = 15 := by rfl
example : iterateN (fun n => n + 3) 4 0 = 12 := by rfl
example : iterateN (addN 2) 4 1 = 9 := by rfl

/- We can easily prove that `applyTwice` is a special case of `iterateN` when `k=2` -/
theorem applyTwiceN_eq_iterateN2 (f : Nat → Nat) :
    applyTwiceN f = iterateN f 2 := by
  rfl


/- __Exercise__ Define the function `pow2` (exponentiation in base 2) using `iterateN` (no recursion!). -/
def pow2 (n : Nat) : Nat := match n with
  | 0 => 1
  | m => iterateN (fun m => 2 * m) m 1

example : pow2 0 = 1 := by rfl
example : pow2 1 = 2 := by rfl
example : pow2 2 = 4 := by rfl
example : pow2 3 = 8 := by rfl


/-
### Fixed points and induction

A value `x` is a *fixed point* of a function `f` when applying `f` to `x` does not change it:

    f x = x

The theorem below says that if the starting value `x` is a fixed point of
`f`, then applying `f` repeatedly any number of times still produces `x`.

This is the first theorem in which one of the parameters is a *proof*:

    h : f x = x

Here `h` is a hypothesis. The theorem says:

    for every f, x, and k,
    if f x = x,
    then iterateN f k x = x.

Equivalently, its statement could be written using an implication:

    ∀ (f : Nat → Nat) (x k : Nat),
      f x = x → iterateN f k x = x

By writing `(h : f x = x)` before the final colon, we give this assumption
a name. The proof may then use `h` whenever it needs evidence that `f x = x`.
-/

theorem iterateN_fixed_point
  (f : Nat → Nat)         -- the function
  (x k : Nat)             -- an arbitrary input and number of repetitions
  (h : f x = x) :         -- hypothesis: x is a fixed point of f
    iterateN f k x = x    -- thesis: iterating f does not change the input x
  := by
  induction k with
  | zero =>
      rfl
  | succ k' ih =>
      rw [iterateN]
      rw [ih]
      exact h

/-
__Exercise__ Prove that `addN n k` is equivalent to `iterateN Nat.succ k n`

Hint: induction on `k`
-/

theorem iterateN_succ_eq_addN (k n : Nat) :
    iterateN Nat.succ k n = addN n k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    simp [iterateN]
    rw [addN_succ_right]
    rw [ih]

/-
__Exercise__ Exploit `iterateN_succ_eq_addN` as an auxiliary lemma (using the `have` tactic) to prove the following.
-/

theorem iterateN_succ_from_zero (k : Nat) :
    iterateN Nat.succ k 0 = k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    simp [iterateN]
    exact ih


end Iteration



section Bounded_experiments

/-
## Higher-order traversals: small data analyses

Before introducing lists, a natural number can represent the finite range

    0, 1, ..., n-1

The higher-order function `sumBelow` takes as input a function `f : Nat → Nat` and
an index `n : Nat`, and computes the summation:

    f 0 + f 1 + ... + f (n - 1)
-/

def sumBelow (f : Nat → Nat) (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => sumBelow f n' + f n'

/- __Exercise__ Resolve the sorry's. -/

example : sumBelow (λ _ => 1) 7 = 7         := by rfl
example : sumBelow (λ n => n) 5 = 10         := by rfl
example : sumBelow (λ n => n) 6 = 15         := by rfl
example : sumBelow (λ n => 2 * n - 1) 6 = 25 := by rfl
example : sumBelow (λ n => 2 * n - 1) 7 = 36 := by rfl

/-
__Exercise (difficulty: 1/4)__ Prove that summing the constant `1` counts the elements in the range.
-/

theorem sumBelow_one (n : Nat) :
    sumBelow (fun _ => 1) n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [sumBelow]
    exact ih

/-
__Exercise__ (**difficulty: 1/4**): define `sumOfSquares` by supplying an
anonymous squaring function to `sumBelow`.  Do not write another recursion.
-/

def sumOfSquares (n : Nat) : Nat :=
  sumBelow (λ x => x * x) n

example : sumOfSquares 0 = 0  := by rfl
example : sumOfSquares 4 = 14 := by rfl
example : sumOfSquares 6 = 55 := by rfl


/-
A function `p : Nat → Bool` can be seen as a predicate on natural numbers.
The function `countBelow` takes as input such a predicate and an index `n : Nat`,
and counts the number of values in the range `0, ..., n-1` that satisfy `p`.
-/

def countBelow (p : Nat → Bool) (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => if p n' then countBelow p n' + 1 else countBelow p n'

example : countBelow isEven 10 = 5 := by rfl


/-
__Exercise (difficulty: 1/4)__ Define the function `anyBelow`, that returns `true`
whenever there **exists** some element in the range `0,...,n-1` that satisfies `p`.
-/
def anyBelow (p : Nat → Bool) (n : Nat) : Bool :=
  match n with
  | 0 => false
  | k + 1 => if p k then true else anyBelow p k

example : anyBelow (fun i => eqN i 7) 10  = true := by rfl
example : anyBelow (fun i => eqN i 11) 10 = false := by rfl
example : anyBelow (fun i => eqN i 10) 10 = false := by rfl

/-
__Exercise (difficulty: 1/4)__ Define the function `allBelow`, that returns `true`
whenever **all** the elements in the range `0,...,n-1` satisfy `p`.
-/

def allBelow (p : Nat → Bool) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | k + 1 => p k && allBelow p k

example : allBelow (fun i => eqN (addN i 0) i) 50 = true := by rfl
example : allBelow (fun i => eqN (doubleN i) i) 10 = false := by rfl
example : allBelow (fun i => ltN i 10) 10 = true := by rfl


end Bounded_experiments



section Exercises


section Exercises_repeated_additions

/-
### Exercise: Repeated additions

In this exercise we study an alternative definition of multiplication based on iterated functions.
-/

/-
__Exercise (difficulty: 1/4)__ Define `repeatAdd k a`, which returns a function that adds `a` to its input `k` times.
-/

def repeatAdd (k a : Nat) : Nat → Nat :=
  iterateN (fun n => n + a) k

example : repeatAdd 3 5 10 = 25 := by rfl
example : repeatAdd 0 5 10 = 10 := by rfl

/-
__Exercise (difficulty: 1/4)__ Prove theorem `repeatAdd_succ_left`. Hint: you do not need induction.
-/

theorem addN_is_Nat_sum (a b : Nat) : addN a b = a + b := by
  induction b with
  | zero => rfl
  | succ k ih =>
    rw [addN_succ_right]
    rw [ih]
    rw [Nat.add_assoc]

-- ASK PROF

theorem repeatAdd_succ_left (a b c : Nat) : repeatAdd (a+1) b c = addN (repeatAdd a b c) b := by
  simp [repeatAdd]
  rw [iterateN]
  rw [addN_is_Nat_sum]


/-
__Exercise (difficulty: 2/4)__ Prove the following equivalence between `repeatAdd` and `mulN`.
-/

theorem repeatAdd_eq_mulN (a b : Nat) : repeatAdd b a 0 = mulN a b := by
  induction b with
  | zero => rfl
  | succ k ih =>
    rw [mulN_succ_right]
    rw [repeatAdd_succ_left]
    rw [ih]

end Exercises_repeated_additions



section Exercises_bounded_search

/-
### Exercise: Bounded search
-/


/-
__Exercise (difficulty: 1/4)__ Prove that if a witness has been found below `n`,
it remains a witness below `n+1`.
-/

theorem anyBelow_grows (p : Nat → Bool) (n : Nat)
    (h : anyBelow p n = true) : anyBelow p (n + 1) = true := by
  simp [anyBelow]
  rw [h]
  simp

/-
__Exercise (difficulty: 2/4)__ Prove that the predicate which always returns `true`
passes on every finite range.
-/

theorem allBelow_true (n : Nat) :
    allBelow (fun _ => true) n = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [allBelow]
    rw [ih]
    rfl

/-
__Exercise (difficulty: 2/4)__ Prove that checking that all values satisfy `p`
is equivalent to checking that there exists no value that does not satisfy `p`.

Hint: by induction on `n`.
-/

theorem allBelow_eq_not_anyBelow_not (p : Nat → Bool) (n : Nat) :
    allBelow p n = !(anyBelow (fun i => !(p i)) n) := by

  induction n with
  | zero => rfl
  | succ k ih =>
    simp [allBelow]
    simp [anyBelow]
    rw [ih]


/-
__Exercise (difficulty: 2/4)__ Prove that checking that if `p` is true for all values,
then `allBelow p` is true up-to any `n`.

Hint: induction on `n`.
-/

theorem allBelow_of_forall
    (p : Nat → Bool)
    (n : Nat)
    (h : ∀ i : Nat, p i = true) :
    allBelow p n := by
  induction n generalizing h with
  | zero => rfl
  | succ i' ih =>
    rw [allBelow]
    rw [h]
    rw [ih]
    simp
    exact h


/-
__Exercise (difficulty: 2/4)__ Exploit `allBelow` to define a bounded test for commutativity.
Namely, `checkCommutativeBelow` checks that the binary operator `op` is commutative from values
in the range `0,...,n-1`.

Hint: since `op` takes two arguments, you will need two uses of `allBelow`.
-/

def checkCommutativeBelow (op : Nat → Nat → Nat) (n : Nat) : Bool :=
  let check := (fun a b => eqN (op a b) (op b a))
  allBelow (fun a => allBelow (check a) n) n



example : checkCommutativeBelow addN 20 = true      := by rfl
example : checkCommutativeBelow Nat.sub 20 = false  := by rfl

/-
__Exercise (difficulty: 2/4)__ Prove that if an operator is commutative, then
`checkCommutativeBelow` is true for all `n`.

Hint: apply `allBelow_of_forall`.
-/
example (op : Nat → Nat → Nat) (n : Nat) :
    (∀ a b : Nat, eqN (op a b) (op b a) = true) → checkCommutativeBelow op n = true := by
    intro h
    apply allBelow_of_forall
    intro a
    apply allBelow_of_forall
    intro b
    exact h a b


end Exercises_bounded_search



section Bank

/-
### Exercise: Bank

We define a `Bank` as a function from accounts to their balances (both represented as `Nat`).
We then introduce operations to deposit and withdraw.
-/

def Bank := Nat → Nat   -- balance of every account (represented as natural numbers)

def emptyBank : Bank := fun _ => 0

def depositBank (a : Nat) (n : Nat) (b : Bank) : Bank :=
  fun x  => if x = a then b a + n else b x

example : depositBank 3 20 emptyBank 3 = 20 := by rfl
example : depositBank 3 20 emptyBank 4 = 0  := by rfl

/- __Exercise (difficulty: 1/4)__ Prove that if a user deposits `n`, then
its balance is increased exactly by `n`. -/

theorem depositBank_same (a : Nat) (n : Nat) (b : Bank) :
    depositBank a n b a = b a + n := by
  unfold depositBank
  simp

/- __Exercise (difficulty: 1/4)__ Prove that if a user deposits `n`, then
the balance of any other account is preserved. -/

theorem depositBank_other
    (a x : Nat) (n : Nat) (b : Bank)
    (h : x ≠ a) :
    depositBank a n b x = b x := by
  unfold depositBank
  simp
  intro h2
  cases h2
  contradiction


/- __Exercise (difficulty: 1/4)__ Define an operation to withdraw from the bank.
If the account does not contain sufficient funds, then the operation has no effect. -/

def withdrawBank (a : Nat) (n : Nat) (b : Bank) : Bank :=
  fun x => if b x >= n && x = a then (b x) - n else b x

example : withdrawBank 3 20  (depositBank 3 100 emptyBank) 3 = 80  := by rfl
example : withdrawBank 3 120 (depositBank 3 100 emptyBank) 3 = 100 := by rfl

/- __Exercise (difficulty: 2/4)__ Prove that two deposits on the same account have the
same effect of a single deposit of the sum of the amounts.

Hint: Use `funext` twice: the first time on the bank `b`, and the second on the account `x`.

The function composition `∘` can be rewritten through `rw [Function.comp_apply]`

Then, use tactic `by_cases` to consider separately the cases where `x = a` and `x ≠ a`.

The tactic

    by_cases h : x = a

creates two goals:

* one with `h : x = a`;
* one with `h : x ≠ a`.

This is useful when the definition being studied contains the same test.
-/

theorem depositBank_additivity (a n1 n2 : Nat) : (depositBank a n2) ∘ (depositBank a n1) = depositBank a (n1 + n2) := by
  funext b
  funext x
  rw [Function.comp_apply]
  by_cases h : x = a
  rw [h]
  simp [depositBank]
  rw [Nat.add_assoc]
  simp [depositBank]
  simp [h]



/- __Exercise (difficulty: 4/4)__ Prove that two withdrawals on the same account have the
same effect of a single withdrawal of the sum of the amounts, provided that the account
has sufficient initial balance.

Hint: Prove two auxiliary lemmas using the `have` tactic:
  h1 : b a ≥ n1
  h2 : b a - n1 ≥ n2
You can prove them with the `omega` tactic, a decision procedure for linear arithmetic.

Then, use tactic `by_cases` to consider separately the cases where `x = a` and `x ≠ a`.

To close the first case, theorem `Nat.sub_sub` may be helpful.
-/

theorem withdrawBank_additivity (a n1 n2 : Nat) (b : Bank) (h : b a ≥ n1 + n2) :
  (withdrawBank a n2) ((withdrawBank a n1) b) = withdrawBank a (n1 + n2) b := by
  have h1 : b a >= n1 := by
    omega
  have h2 : b a - n1 >= n2 := by
    omega
  funext x
  by_cases h3 : x = a
  simp [withdrawBank]
  simp [h3, h, h1, h2]
  rw [Nat.sub_sub]
  simp [withdrawBank]
  simp [h3]


end Bank


section Closed_form_summations

/-
### Exercise: Closed-form summations
-/


/-
__Exercise (difficulty: 3/4)__ Prove that the sum of the first `n` odd numbers is `n²`.
The initial value at index zero contributes zero because subtraction on `Nat` stops at zero.
-/

theorem sumOdd_closed (n : Nat) : sumBelow (λ n => 2 * n - 1) (n+1) = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumBelow]
    rw [ih]
    simp [Nat.mul_add]
    simp [Nat.add_mul]
    simp [Nat.add_assoc]
    rw [Nat.two_mul]
    rw [Nat.add_assoc]


/-
__Exercise (difficulty: 3/4)__ Prove the following closed-form formula for the summation of numbers.
-/

theorem sumId_closed (n : Nat) : 2 * (sumBelow (λ n => n)) (n+1) = (n+1) * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [sumBelow]
    simp [Nat.mul_add]
    simp [Nat.add_mul]
    simp [sumBelow] at ih
    simp [Nat.mul_add] at ih
    simp [Nat.add_mul] at ih
    rw [ih]
    simp [Nat.two_mul]
    simp [Nat.add_assoc]


end Closed_form_summations


end Exercises
