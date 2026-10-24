/-
The following `import` is used to bring here the definitions of the previous lecture.

If you are working on `https://live.lean-lang.org/`, then remove the `import` and
copy-and-paste the code of the previous lecture before this one.
-/
import pl_lean.l2


set_option autoImplicit false


/-
# Structural induction

In the previous lecture we defined recursive functions on natural numbers.
In this lecture we learn the corresponding proof technique: *structural induction*.

By the end of the lecture, you should be able to:

* recognize when case analysis is insufficient and induction is needed;
* identify the base case, inductive case, and induction hypothesis;
* choose an induction variable by looking at the recursive definition involved;
* use `rw`, `exact`, and `simp` together with an induction hypothesis;
* perform structural induction on other structured data beyond `Nat`.
-/


section Induction

/-
## Induction: the proof counterpart of recursion

We noted in the previous lecture that case analysis is not enough to prove `addN 0 n = n`:
in the successor case we get the goal for `k + 1`, but to solve it we need to know the
result for `k`. This is exactly what *mathematical induction* provides.

Suppose we want to prove a property `P n` for every natural number `n`.
The induction principle says that it is enough to prove:

1. `P 0`                       -- the base case;
2. `P n -> P (n + 1)`          -- the inductive case.

The second part says that if the property is true for an arbitrary `n`, then
it is true for its successor.

In Lean, the `induction` tactic exposes exactly these cases.  In the inductive case,
we also get the *induction hypothesis* `ih`: the statement for the smaller number.

-/

#check addN_succ_right    -- this lemma will be used in the proof: check it

theorem zero_addN (n : Nat) : addN 0 n = n := by
  induction n with
  | zero => rfl               -- base case
  | succ n' ih =>             -- inductive case (note `ih` in the Infoview)
      rw [addN_succ_right]    -- addN 0 (n' + 1) -> (addN 0 n') + 1
      rw [ih]

/-
Let's follow the proof.  After `induction n with`, Lean shows two goals:

    case zero:   addN 0 0 = 0
    case succ:   ih : addN 0 n' = n'
                 ⊢ addN 0 (n' + 1) = n' + 1

* The first goal follows by computation, so `rfl` works.
* In the second goal, we use two rewritings:
  1. `rw [addN_succ_right]` rewrites `addN 0 (n' + 1)` into `addN 0 n' + 1`.
  2. `rw [ih]` replaces `addN 0 n'` by `n'`, and the goal becomes `n' + 1 = n' + 1`,
     which `rw` closes by itself (with no explicit use of `rfl`).

This proof highlights an important correspondence:

    PROGRAMMING                  PROVING
    ------------------------------------------------
    match n with ...             cases n with ...
    recursive call on n'         induction hypothesis about n'
    base case                    base case
    recursive case               inductive case

The proof has the same shape as the recursive function it talks about.

-/

/-
### Choosing the induction variable

As another example, we consider a variant of `addN_succ_right` where the
successor is in the first argument.  The theorem contains two variables, so we
must decide which one to induct on.

The useful choice is `m`, because `addN` examines its second argument.  After
splitting `m` into `0` and `m' + 1`, the defining equations of `addN` become
available, and the induction hypothesis describes exactly the recursive call.

A useful rule of thumb is:

    Look at the definition that is stuck, and induct on the argument on which
    that definition recurses.

As an experiment, try replacing `induction m` below with `induction n` and
inspect the resulting induction hypothesis.  Lean accepts the command, but the
hypothesis does not describe the recursive call that we need.
-/

theorem addN_succ_left (n m : Nat) : addN (n + 1) m = addN n m + 1 := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    rw [addN_succ_right]      -- rewrite addN_succ_right in the left-hand side of =
    rw [addN_succ_right]      -- rewrite addN_succ_right in the right-hand side of =
    rw [ih]

/-
In the previous proof, we could have just written:
  | succ m' ih => rw [addN_succ_right,addN_succ_right,ih]
I split the rewritings in three steps so that you can check their effects in the Infoview.

Tactic proofs of this shape are often written in a shorter way using `simp`,
which repeatedly rewrites using the definitions and lemmas we give it.  For
example, the inductive case above could be written

    | succ m' ih => simp [addN, ih]

We will use both styles.  The explicit `rw` version is better for understanding
the proof step-by-step, `simp` is faster to write.
-/

/-
We can now prove commutativity of our addition function.
-/

theorem addN_comm (n m : Nat) : addN n m = addN m n := by
  induction m with
  | zero =>
    rw [addN_zero]
    rw [zero_addN]
  | succ m' ih =>
    rw [addN_succ_right]
    rw [addN_succ_left]
    rw [ih]

/-
The proof above is a useful milestone.  We have gone from a short recursive
program to a mathematical property about the program, and Lean has checked the
proof mechanically.
-/

end Induction



section Boolean_expressions

/-
## Structural induction is not only induction on numbers

The shape of an induction proof is determined by the constructors of the type.
For `Nat`, values form a linear chain:

    0, succ 0, succ (succ 0), ...

Consequently, the inductive case has one smaller value and one induction
hypothesis.  Other inductive types can branch.

As an example, consider the syntax of Boolean expressions:

    t ::= true | false | if t₀ then t₁ else t₂

This is a tree-shaped datatype.  An `if` expression contains three smaller
Boolean expressions.
-/

inductive BExp where
  | btrue  : BExp
  | bfalse : BExp
  | bifte  : BExp → BExp → BExp → BExp
  deriving Repr

/-

The function `evalBExp` evaluates a Boolean expression by structural recursion.
It follows the same clauses as the *big-step semantics*.

Writing `t ⇒ v` for "expression `t` evaluates to Boolean value `v`", the rules
would be:

-----------------          ------------------
  btrue ⇒ true               bfalse ⇒ false

  t0 ⇒ true    t1 ⇒ v          t0 ⇒ false    t2 ⇒ v
-------------------------      --------------------------
 bifte t0 t1 t2 ⇒ v             bifte t0 t1 t2 ⇒ v

Here we implement those rules as a function, since we already know that every expression
has one uniquely determined Boolean result. In later lectures, we will formalize
operational semantics as inductively defined relations.

-/

def evalBExp : BExp → Bool
  | .btrue          => true
  | .bfalse         => false
  | .bifte t0 t1 t2 => if evalBExp t0 then evalBExp t1 else evalBExp t2


example :
    let ex0 := .bifte (.bifte .bfalse .btrue .bfalse) .btrue .bfalse
    evalBExp ex0 = false := by rfl

/-
Here is another structurally recursive function.  `dualBExp` exchanges `true` and `false`.
At every conditional, it dualizes the condition and also swaps the two branches.
-/

def dualBExp : BExp → BExp
  | .btrue        => .bfalse
  | .bfalse       => .btrue
  | .bifte t0 t1 t2 =>
      .bifte (dualBExp t0) (dualBExp t2) (dualBExp t1)

/-
Applying `dualBExp` twice gives back the original expression.  The proof uses
structural induction on `t`.

There are three cases, one for each constructor.  Note that the `bifte` case
supplies *three* induction hypotheses, because `bifte` has three recursive arguments:

    ih0 : dualBExp (dualBExp t0) = t0
    ih1 : dualBExp (dualBExp t1) = t1
    ih2 : dualBExp (dualBExp t2) = t2

This is the main difference from induction on `Nat`, whose `succ` constructor
has only one recursive argument.
-/

theorem dualBExp_involutive (t : BExp) : dualBExp (dualBExp t) = t := by
  induction t with
  | btrue   => rfl
  | bfalse  => rfl
  | bifte t0 t1 t2 ih0 ih1 ih2 =>
      rw [dualBExp]         -- unfold the outer application of dualBExp
      rw [dualBExp]         -- unfold the remaining application
      rw [ih0, ih1, ih2]    -- applies the three induction hypotheses

/-
In the `bifte` case, the first two rewrites compute the two applications of
`dualBExp`.  The resulting goal contains one double application for each
subtree.  The final line uses the three induction hypotheses to replace those
expressions by `t0`, `t1`, and `t2`.

Structural induction follows the declaration of the datatype:

* one proof case is generated for every constructor;
* one induction hypothesis is generated for every recursive constructor argument.

Induction is not specifically about numbers.  It is a way of proving a
property for every finite value generated by an inductive definition.
-/

end Boolean_expressions



section Exercises

/-
## Exercises

The difficulty labels are relative to this lecture:

* **1/4 -- warm-up:** one idea or direct computation;
* **2/4 -- standard:** a routine induction with a useful induction hypothesis;
* **3/4 -- substantial:** several lemmas or an additional case split;
* **4/4 -- challenge:** proof planning and a longer chain of rewrites.

The exercises are grouped by topic, not strictly by difficulty.  A good first
route is to do all exercises rated 1/4 and 2/4, then return to the harder
multiplication and syntax-tree exercises.  Difficulty also depends on how many
hints you use.

-/


/-
### Exercise: Adding successors

**Difficulty: 1/4 (warm-up).**

This does not require induction.  Use `addN_succ_right` and `addN_succ_left`.
-/

theorem addN_self_succ (n : Nat) : addN (n + 1) (n + 1) = addN n n + 1 + 1 := by
  simp [addN]
  rw [addN_succ_left]

/-
### Exercise: Associativity of addN

**Difficulty: 2/4 (standard induction).**

Prove that `addN` is associative.

Hint: induction on `k`.  In the successor case, unfold the additions with
`addN_succ_right`, and finish with the induction hypothesis.
-/

theorem addN_assoc (n m k : Nat) : addN (addN n m) k = addN n (addN m k) := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    simp [addN]
    exact ih

/-
### Exercise: Zero is left-absorbing for mulN

**Difficulty: 2/4 (standard induction).**

Prove that multiplying by zero on the left gives zero.
Hint: induct on `n`.  In the successor case, rewrite with
`mulN_succ_right`, then use the induction hypothesis.  The remaining equality
holds by computation.
-/

theorem mulN_zero_left (n : Nat) : mulN 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp [mulN]
    rw [addN_zero]
    exact ih

/-
### Exercise: One is left-identity for mulN

**Difficulty: 2/4 (standard induction).**

Prove that one is a left identity for `mulN`.

Hint: induct on `n`.  In the successor case, use `mulN_succ_right` and the induction
hypothesis.  The remaining equality follows by computation.
-/

#check mulN_succ_right

theorem mulN_one_left (n : Nat) : mulN 1 n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [mulN]
    rw [ih]
    rfl

/-
### Exercise: Multiplication of a successor (left)

**Difficulty: 4/4 (challenge).**  It is reasonable to skip this on a first pass.

The definition of `mulN` recurses on its *second* argument, so `mulN (n + 1) m`
cannot be computed until we know something about `m`.  Therefore:

Hint 1: proceed by induction on `m`.

Hint 2 (base case): use `mulN_zero_right`.

Hint 3 (successor case): write `x` for `mulN n m'` and follow the goal in the
Infoview.  The proof has three phases.

1. Unfold the multiplications: rewrite with `mulN_succ_right`.  It must be
   used twice, once for each side.  Then use the induction hypothesis `ih`
   to remove the remaining `mulN (n + 1) m'`.  Now both sides are additions
   of `x` and the two numbers `m'` and `n`:

       addN (addN x m') (n + 1)  =  addN (addN x n) (m' + 1)

2. Pull out the successors: rewrite with `addN_succ_right` (twice).  Now both
   sides end with `+ 1`.

3. The numbers `m'` and `n` appear in a different order on the two sides.
   This is not a computation: we need *associativity* and *commutativity* of
   addition.  Use `addN_assoc` (twice) to regroup both sides as
   `addN x (addN _ _)`, and `addN_comm` with explicit arguments to swap
   `m'` and `n`.
-/

theorem mulN_succ_left (n m : Nat) : mulN (n + 1) m = addN (mulN n m) m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp [mulN_succ_right]
    rw [ih]
    simp [addN]
    rw [addN_assoc]
    rw [addN_assoc]
    rw [addN_comm n k]


/-
### Exercise: Commutativity of mulN

**Difficulty: 2/4 once `mulN_succ_left` is available.**

Prove that multiplication is commutative (theorem `mulN_comm`).

Hint: in the inductive case, exploit `mulN_succ_right` and `mulN_succ_left`.
-/

theorem mulN_comm (n m : Nat) : mulN n m = mulN m n := by
  induction m with
  | zero =>
    rw [mulN_zero_left]
    rfl
  | succ m' ih =>
    rw [mulN_succ_right]
    rw [ih]
    rw [mulN_succ_left]

/-
### Exercise: Multiplication distributes over addition (left)

**Difficulty: 3/4 (substantial).**

Prove that multiplication distributes over addition:

    a * (b + c)  =  a * b + a * c

Which variable should we induct on?  Look at the definitions:

* `mulN a n` recurses on its *second* argument `n`;
* `addN b c` recurses on its second argument `c`.

In the left-hand side `mulN a (addN b c)`, the number `addN b c` is the second
argument of `mulN`.  If `c` is a successor, then `addN b c` is a successor too,
and `mulN` can then unfold.  So the natural choice is induction on `c`.
-/

theorem mulN_addN_distrib_left (a b c : Nat) : mulN a (addN b c) = addN (mulN a b) (mulN a c) := by
  induction c with
  | zero => rfl
  | succ k ih =>
    rw [addN_succ_right, mulN_succ_right, mulN_succ_right]
    rw [ih]
    rw [addN_assoc]

/-
#### Optional challenge: choose a less convenient induction variable

**Difficulty: 4/4.**

The following proof establishes the same result by induction on `a`.  This
choice is valid, but it needs substantially more algebraic rearrangement.  It
illustrates why choosing the variable that controls the stuck recursive
definition usually leads to a clearer proof.
-/

theorem mulN_addN_distrib_left_by_first_arg (a b c : Nat) :
    mulN a (addN b c) = addN (mulN a b) (mulN a c) := by
  sorry


/-
### Exercise: Associativity of mulN

**Difficulty: 3/4 (substantial).**

Prove that multiplication is associative (theorem `mulN_assoc`).

Hint: in the inductive case, exploit `mulN_addN_distrib_left`.
-/

theorem mulN_assoc (n m k : Nat) : mulN (mulN n m) k = mulN n (mulN m k) := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    rw [mulN_succ_right]
    rw [mulN_succ_right]
    rw [ih]
    rw [mulN_addN_distrib_left]


/-
### Exercise: Reflexivity of eqN

**Difficulty: 1/4 (warm-up).**

Prove that `eqN` is reflexive.  Hint: proceed by induction on `a`, and use the
`exact` tactic.
-/

theorem eqN_refl (a : Nat) : eqN a a = true := by
  induction a with
  | zero => rfl
  | succ n ih =>
    simp [eqN]
    exact ih


/-
### Exercise: Reflexivity of leN

**Difficulty: 1/4 (warm-up).**

Prove that every natural number is less than or equal to itself.  The proof has
the same inductive shape as `eqN_refl`.

def leN : Nat → Nat → Bool
  | 0,     _     => true
  | _ + 1, 0     => false
  | n + 1, m + 1 => leN n m

-/

theorem leN_refl (n : Nat) : leN n n = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [leN]
    exact ih


/-
### Guided example: induction with generalizing

This guided example introduces a variant of the `induction` tactic
that often arises when dealing with multiple induction candidates.

We'd like to prove that the less than or equal relation between two natural
numbers is preserved by incrementing the right term:
-/

theorem leN_succ_right_sorry (a b : Nat) :
  leN a b = true → leN a (b + 1) = true := by

/-
The proof is more delicate than the others with standard induction as it
requires the notion of _generalizing_ a variable.

A side-effect of declaring the arguments of `a` and `b` on the left side
of the colon `:` is that they're already introduced in the proof context,
forcing us to work with fixed values for both for the rest of the proof.

To see why it matters, let's try proceeding naively by inducting on `a`:
-/
  intro h
  induction a with
  | zero => rfl
  | succ a' ih => cases b with
    | zero => cases h
    | succ b' =>
      rw [leN];
      rw [leN] at h
      sorry

/-
Here we get stuck (look at the proof context with the cursor on `sorry`).

After simplifying the definition of `leN`, we have a proof of
`h : leN a' b' = true` which almost matches the premise of the
inductive hypothesis if not for the second argument, which became
`b' + 1` after doing case analysis on `b`.

The inductive hypothesis is too weak to prove our goal: it should hold for any
value as the second argument of `leN` and not just the `b` that was fixed at
the beginning of the proof. What's worse, doing case analysis on `b` specialized
the inductive hypothesis even more.

What we need to complete the proof is an inductive hypothesis that works
for any natural number `b`. Let's scratch the previous naive attempt and
start a new one.

We can ask Lean to produce such a stronger inductive hypothesis that is
universally quantified on `b` by writing `induction a generalizing b` before
the `with` keyword.

In the proof below, move the cursor after the arrow of the inductive case.
Notice the inductive hypothesis now has `∀ (b : Nat)`, meaning it works
for any natural number as the second operand of `leN`, while the first
operand `a'` remains fixed.

After doing case analysis on `b` and simplifying the definition of `leN`, we
can finally apply the proof `h : leN a' b' = true` to the IH, instantiating its
`b` parameter with `b'`, which will give us the goal.

Therefore, `exact ih b' h` closes the proof.
-/
theorem leN_succ_right (a b : Nat) : leN a b = true → leN a (b + 1) = true := by
  intro h
  induction a generalizing b with
  | zero => rfl
  | succ a' ih => cases b with
    | zero => cases h
    | succ b' =>
      rw [leN];
      rw [leN] at h;
      exact ih b' h

/-
By the way, an equivalent theorem is available in Lean's standard library
under the name `Nat.le_succ_of_le`.
-/

#print Nat.le_succ_of_le


/-
### Exercise: Interplay of leN and successor: left increment

**Difficulty: 3/4 (induction with generalize).**

Prove that the less than or equal relation between two natural numbers is also
preserved by incrementing the left term, or, equivalently, if `a` is strictly
less than `b` then it is also less than or equal to `b`.

In Lean's standard library this is known as `Nat.le_of_succ_le`.

Hint: induction on `b` generalizing `a`. In the inductive case,
do case-analysis on `a`.
-/
theorem leN_succ_left (a b : Nat) : leN (a + 1) b = true → leN a b = true := by
  intro h
  induction b generalizing a with
  | zero =>
    rw [leN_eq_eqN_zero]
    rw [leN_eq_eqN_zero] at h
    cases h
  | succ k ih =>
    cases a with
      | zero =>
        simp [leN]
      | succ a' =>
        rw [leN]
        rw [leN] at h
        exact ih a' h

/-
### Exercise: Antisymmetricity of leN

**Difficulty: 4/4 (challenge).**

Prove that `leN` is antisymmetric.

Hint: do `intro n` first, then induct on `n`, so that `m` stays quantified in
the induction hypothesis.  Then split `m` with `cases`: the mixed cases
(`zero` with `succ`, `succ` with `zero`) have a false hypothesis.
In the `succ`, `succ` case, use the induction hypothesis.

Note that you don't need to generalize `m` if you intro and induct on `n`
immediately as recommended, because the proposition has `m` universally
quantified.
-/

theorem leN_antisymm : ∀ n m, leN n m → leN m n → eqN n m := by
  intro n
  induction n with
  | zero =>
    intros m h h1
    cases m with
    | zero => rfl
    | succ m' => cases h1
  | succ k ih =>
    intro m
    intros h h1
    cases m with
    | zero =>
      simp [eqN]
      cases h
    | succ m' =>
      rw [eqN.eq_4]
      exact ih m' h h1


/-
### Exercise: Subtracting a number from itself

**Difficulty: 1/4 (warm-up).**

Prove the following property by induction on `n`.  In the successor case, the
definition of `subN` reduces the goal to the induction hypothesis.

def subN : Nat → Nat → Nat
  | 0,     _     => 0
  | n + 1, 0     => n + 1
  | n + 1, m + 1 => subN n m

-/

theorem subN_self (n : Nat) : subN n n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [subN]
    exact ih


/-
### Exercise: Alternative characterization of even (n + 1)

**Difficulty: 2/4 (standard induction).**

Prove that `isEven (n + 1)` is the Boolean negation of `isEven n`.
Hint: `simp` knows that `!` is involutive.
-/

theorem isEven_succ (n: Nat) : isEven (n+1) = !(isEven n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [ih]
    simp [isEven]


/-
### Exercise: Doubled numbers are even

**Difficulty: 2/4 (standard induction).**

Hint: by induction on `n`.
-/

theorem isEven_doubleN (n: Nat) : isEven (doubleN n) := by
  induction n with
  | zero => sorry
  | succ k ih =>
    rw [doubleN]
    rw [addN_succ_right, addN_succ_left]
    rw [<- doubleN]
    rw [<- ih]
    rfl


/-
### Exercise: Double and addN

**Difficulty: 2/4 (standard induction with earlier lemmas).**

Hint: induct on `n`.  In the successor case, rewrite with the induction
hypothesis, `addN_succ_right`, and `addN_succ_left`.
-/

theorem doubleN_addN (n: Nat) : doubleN n = addN n n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [doubleN]

/-
### Exercise: Correctness of dualBExp

**Difficulty: 3/4 (induction followed by Boolean case analysis).**

Prove that `dualBExp` negates the Boolean value of an expression.

Hint: use structural induction on `t`.  In the `bifte` case you will need the
three induction hypotheses.  It is also useful to consider the two possible
values of `evalBExp t0` with

    cases h : evalBExp t0 with ...

After the case split, both sides compute to the same Boolean expression, so
`rfl` finishes each case.
-/

theorem evalBExp_dual (t : BExp) : evalBExp (dualBExp t) = !(evalBExp t) := by
  induction t with
  | btrue => rfl
  | bfalse => rfl
  | bifte t0 t1 t2 ih0 ih1 ih2 =>
    simp [dualBExp]
    simp [evalBExp]
    rw [ih0, ih1, ih2]
    simp
    cases h : evalBExp t0 with rfl


/-
### Exercise (long): Boolean connectives

**Difficulty: 4/4 overall (extended exercise).**  The individual tasks below
start gently and build toward a semantic-preservation proof.

Earlier we defined `BExp`, a language with three constructs:

    btrue                  the constant true
    bfalse                 the constant false
    bifte c t e            "if c then t else e"

and its evaluation function `evalBExp : BExp → Bool`.

Here we define a second language, `BExpConn`, which uses the logical
*connectives* instead of the conditional:

    btrue                  the constant true
    bnot t                 negation
    band t0 t1             conjunction
    bor t0 t1              disjunction

Both languages are inductive types, so we define their evaluation by structural recursion.
For `BExpConn` each equation uses the corresponding Boolean operator of Lean: `!`, `&&`, `||`.
-/

inductive BExpConn where
  | btrue  : BExpConn
  | bnot   : BExpConn → BExpConn
  | band   : BExpConn → BExpConn → BExpConn
  | bor    : BExpConn → BExpConn → BExpConn
  deriving Repr


/-
__Exercise (difficulty 1/4):__ Define the evaluation function for `BExpConn`.
-/
def evalBExpConn : BExpConn → Bool := sorry

example :
    let ex0 := .band (.bor (.bnot .btrue) .btrue) .btrue
    evalBExpConn ex0 = true := by sorry

example :
    let ex1 := .band (.bor (.bnot .btrue) .btrue) (.bnot .btrue)
    evalBExpConn ex1 = false := by sorry

/-
Every connective can be expressed with a conditional:

    not a     =  if a then false else true
    a and b   =  if a then b else false
    a or b    =  if a then true else b

__Exercise (difficulty 2/4):__ Define a function `bexpconn_to_bexp` that translates
`BExpConn` terms into `BExp` terms, following the intuition above.
-/

def bexpconn_to_bexp : BExpConn → BExp := sorry


-- __Exercise (difficulty 1/4):__ Test the translation on the two examples above.

example :
    let ex0 := .band (.bor (.bnot .btrue) .btrue) .btrue
    evalBExpConn ex0 = evalBExp (bexpconn_to_bexp ex0) := by sorry

example :
    let ex1 := .band (.bor (.bnot .btrue) .btrue) (.bnot .btrue)
    evalBExpConn ex1 = evalBExp (bexpconn_to_bexp ex1) := by sorry

/-
__Exercise (difficulty 3/4):__ Prove that the translation preserves the meaning:
evaluating a term in `BExpConn` gives the same Boolean as evaluating
its translation in `BExp`.

Hint: use structural induction.  In each recursive case, first rewrite with the
induction hypotheses.  Then split on the Boolean value of the translated first
subexpression.  The syntax `cases h : e` performs the split and records an
equation for `e`, allowing the surrounding conditional to compute.

-/

theorem bexpconn_equiv_bexp (t : BExpConn) : evalBExpConn t = evalBExp (bexpconn_to_bexp t) := by
  sorry

end Exercises


section Binary_numbers

/-
## Binary numbers (optional extended exercise)

**Difficulty: 4/4 overall.**  The early programming tasks are approachable,
but the complete sequence is long.  It works well as optional laboratory work
or as a challenge for students who finish the core exercises.

Natural numbers can be written in binary.  We define a new inductive type of
binary numbers with three constructors:

    bz        the number 0
    b0 n      append the digit 0:  the number 2 * n
    b1 n      append the digit 1:  the number 2 * n + 1

The least significant digit is the *outermost* constructor.  For example:

    0  =  bz
    1  =  b1 bz
    2  =  b0 (b1 bz)
    3  =  b1 (b1 bz)
    4  =  b0 (b0 (b1 bz))
    5  =  b1 (b0 (b1 bz))
    6  =  b0 (b1 (b1 bz))

Check one of them by hand: `b0 (b1 (b1 bz))` is twice the number `b1 (b1 bz)`,
which is `2 * 1 + 1 = 3`, so it is 6.

This datatype also admits representations with leading zeroes.  For example,
both `bz` and `b0 bz` denote zero.  Thus `binToNat` is not injective on every
`BinNat`.  The function `natToBin` below produces canonical representations;
we will prove the conversion direction that remains true without first defining
a separate predicate for canonical numerals.
-/

inductive BinNat where
  | bz : BinNat
  | b0 : BinNat → BinNat
  | b1 : BinNat → BinNat
  deriving Repr

/-
In the rest of the exercise we write binary values using Lean's dot notation
for constructors, which allows to build larger values of an inductive type by
appending its unary constructors on the right of an existing value with a dot,
avoiding the need to wrap nested values in parentheses.

In the case of our binary numbers, it also allows to write them in the more
natural notation where the most significant digits appear on the left.
-/

def bz := BinNat.bz           -- shorthand to avoid repeating BinNat.bz

def six := bz.b1.b1.b0
def six' := bz.b0.b0.b0.b0.b0.b1.b1.b0
def thirteen := six.b1
def twentyfour := six'.b0.b0


/-
### Task 1: Converting binary to natural

**Difficulty: 1/4 (warm-up programming).**

Write a function `binToNat` that converts a `BinNat` into a `Nat`.
-/

def binToNat : BinNat → Nat := sorry

example : binToNat bz.b1.b1.b0 = 6 := by sorry


/-
### Task 2: Incrementing a binary number

**Difficulty: 2/4 (recursive programming with carry).**

Write a function `binIncr` that adds one *directly on numerals*, as in a binary counter:
* zero becomes `1`;
* a numeral ending in `0` has its last digit changed to `1`;
* a numeral ending in `1` becomes `0` and *carries* to the rest.
-/

def binIncr : BinNat → BinNat := sorry

example : binToNat (binIncr bz.b1.b1.b0) = 7 := by sorry

/-
### Task 3: Converting natural to binary

**Difficulty: 2/4 (recursive programming).**

Write a function `natToBin` that converts a `Nat` into a `BinNat`
by counting up from zero.
-/

def natToBin : Nat → BinNat := sorry

example : natToBin 6 = bz.b1.b1.b0 := by sorry
example : natToBin 11 = bz.b1.b0.b1.b1 := by sorry


/-
### Task 4: Correctness of binary increment (1)

**Difficulty: 1/4 (computation).**

Consider the following diagram:

                  succ
        n:Nat ----------------> n':Nat
          |                       |
 natToBin |              natToBin |
          |                       |
          v       binIncr         v
        b:BinNat -------------> b':BinNat

Prove that the diagram *commutes*, that is the two paths to b' are equivalent.
-/

theorem natToBin_succ (n : Nat) : natToBin (n + 1) = binIncr (natToBin n) := by
  sorry


/-
### Task 5: Defining doubling

**Difficulty: 2/4 (case analysis in a definition).**

Define `binDouble`, which doubles a numeral *directly on numerals*, without
converting to `Nat`.  Zero must stay `bz` (we do not want a leading zero digit):

    binDouble bz     = bz
    binDouble (b0 n) = b0 (b0 n)
    binDouble (b1 n) = b0 (b1 n)
-/

def binDouble : BinNat → BinNat := sorry

example : binDouble .bz = .bz := by sorry
example : binDouble (.b1 .bz) = .b0 (.b1 .bz) := by sorry
example : binToNat (binDouble (.b1 (.b1 .bz))) = 6 := by sorry


/-
### Task 6: Correctness of doubling

**Difficulty: 1/4 (case analysis).**

Prove that `binDouble` really doubles the number represented.
Hint: no induction is needed.  There are three constructors, so use `cases`.
-/

theorem binToNat_binDouble (b : BinNat) :
    binToNat (binDouble b) = 2 * binToNat b := by
  sorry

/-
### Task 7: Correctness of binary increment (2)

**Difficulty: 3/4 (induction plus linear arithmetic).**

Consider the following diagram:

                    binIncr
        b:BinNat -------------> b':BinNat
          |                       |
 binToNat |              binToNat |
          |                       |
          v         succ          v
        n:Nat ----------------> n':Nat

Prove that the diagram *commutes*, that is the two paths to n' are equivalent.

Hint: use the tactic `omega` on goals involving arithmetic on natural numbers.
This tactic proves equations and inequalities of linear arithmetic on `Nat`,
using the hypotheses in the context.  Here induction handles the recursive
structure, while `omega` handles only the final arithmetic rearrangement; it
does not replace the induction.
-/

theorem binToNat_binIncr (b : BinNat) :
    binToNat (binIncr b) = binToNat b + 1 := by
  sorry


/-
### Task 8: Converting a number to binary and back

**Difficulty: 2/4 once Task 7 is available.**

Prove that converting a number to binary and back gives the same number.

Hint: induction on `n`.  The successor case needs `natToBin_succ`,
`binToNat_binIncr` from Task 7, and the induction hypothesis.  You can use them with
`rw [natToBin_succ, binToNat_binIncr, ih]`.
-/

theorem binToNat_natToBin (n : Nat) : binToNat (natToBin n) = n := by
  sorry


/-
### Task 9: Normalizing a binary number

**Difficulty: 4/4 overall.**

The previous theorem proves that `binToNat` is a left inverse for `natToBin`.

However, since `binToNat` is not injective (for example, it sends both
`.b1 .bz` and `.b1 .b0 .bz` to the natural 1), or equivalently since `natToBin`
is not surjective, `binToNat` is not a right inverse for `natToBin`,
meaning the composition `natToBin ∘ binToNat` is not the identity.
-/

def normalize (b : BinNat) : BinNat := natToBin (binToNat b)

/-
It serves nonetheless as a "normalizing" function that given a binary
number produces its canonical representation, where the number
has been stripped of any leading zeros.

Replace the `sorry`'s below with `rfl` to check that your `normalize`
behaves correctly.
-/

example : normalize bz.b0 = bz := by sorry
example : normalize bz.b0.b0.b0.b1 = bz.b1 := by sorry
example : normalize six = six := by sorry

example : binToNat (normalize bz.b0.b0.b0.b1) = 1 := by sorry
example : binToNat (normalize six) = 9 := by sorry

/-
We can define a function that tests if a binary number has one or more
leading zeros: it suffices to check for the pattern `.b0 .bz`.
-/

def hasLeadingZeros : BinNat → Bool
| .bz => false
| .b0 .bz => true
| .b0 b => hasLeadingZeros b
| .b1 b => hasLeadingZeros b

example : hasLeadingZeros bz.b0 = true := by rfl
example : hasLeadingZeros six = false := by rfl
example : hasLeadingZeros six' = true := by rfl
example : hasLeadingZeros bz.b0.b0.b1.b0.b0.b1.b0.b0.b1 = true := by rfl
example : hasLeadingZeros bz.b1.b0.b0.b1.b0.b0.b1.b0.b0.b1 = false := by rfl

/-
The goal of this exercise is to prove that `normalize` actually computes
the smallest possible representation of the binary number.

First, we prove a few auxiliary theorems that'll help us arrive at the
main result.
-/

/-
#### Sub-task 1 - Difficulty: 2/4 (simplification).

An algebraic equality between `binDouble` and `binIncr` needed for the
next theorem.

Hint: induction not necessary, simplify by the definitions `binDouble` and `binIncr`.
-/
theorem binIncr_binDouble (b : BinNat) :
    binDouble (binIncr b) = binIncr (binIncr (binDouble b)) := by
  sorry


/-
#### Sub-task 2 - Difficulty: 3/4 (standard induction and linear algebra).

A useful equality between `binDouble` and `binToNat`: we get the same number
by  either doubling the binary result or doubling the natural argument of
`natToBin` with the respective operations.

Hint: induct on `n`; in the inductive case simplify with `Nat.mul_succ`
and `natToBin`, then rewrite with the IH and `binIncr_binDouble`.
-/
theorem binDouble_binToNat (n : Nat) :
    binDouble (natToBin n) = natToBin (2 * n) := by
  sorry


/-
#### Sub-task 3 - Difficulty: 2/4 (standard induction).

Prove that your implementation of `binDouble` preserves the result of
`hasLeadingZeros` on its argument.

This will help you prove one of the inductive cases of the boss theorem.
-/

theorem binDouble_hasLeadingZeros (b : BinNat) :
    hasLeadingZeros (binDouble b) = hasLeadingZeros b := by
  sorry


/-
#### Sub-task 4 - Difficulty: 4/4 (boss challenge).

Prove that `normalize` computes the smallest possible representation:
the binary it returns does not have any leading zero.

Hints:

1. Induction on `b`. In both inductive cases, rewrite `binDouble_binToNat`
   to eliminate the `2 * n` multiplication.

2. In the `b0 b'` case, rewrite `binDouble_hasLeadingZeros`.

3. In the `b1 b'` case, do case analysis on `normalize b'` recording the
   equality for the constructor instance with the syntax
   `cases eq : normalize b' with`.
-/

theorem normalize_smallest (b : BinNat) :
    hasLeadingZeros (normalize b) = false := by
  sorry


end Binary_numbers
