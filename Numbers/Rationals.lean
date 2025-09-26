-- import Mathlib.Tactic
import Numbers.Integers

/-!

All the original work is by Kevin Buzzard.

# The rationals

In this file we build the rationals from scratch.

The strategy is to observe that every rationals can be written as `a / b`
for `a` and `b` integers witb `b ≠ 0`, so we define the "pre-rationals" to
be `MyInt × (MyInt - {0})`, the pairs `(a, b)` of integers. We define an equivalence
relation `≈` on `MyInt × (MyInt - {0})`, with the idea being that `(a, b) ≈ (c, d)`
if and only if `a / b = c / d`. This doesn't make sense yet, but the equivalent
equation `a * d = b * c` does. We prove that this is an equivalence relation,
and define the rationals to be the quotient.

## The field structure on the rationals

We extend addition, subtraction and multiplication to the rationals, and also
define division. We then prove that the rationals are a field. The proofs are all of
the form "reduce to a question about integers, and then solve it using tactics
which prove theorems about integers".

## The ordering on the integers

In the file `RationalGameOrder.lean` we define an ordering on the rationals,
prove that it is total, and that it plays well with the ring structure
defined in this file.
-/


-- Comment: Having the denominator be ≠ 0 instead of > 0 is really annoying and leads to a lot of duplicate code.
-- Maybe as a defition it's okay and then there could be glue for turning the denominator to be strictly positive

/-!

## The pre-rationals

### Denominator API

-/
/-- The multiplication of non-zero MyInts is closed -/
instance : Mul {x : MyInt // x ≠ 0} where
  mul a b := ⟨a.1 * b.1, mul_ne_zero a.2 b.2⟩

@[simp, norm_cast] lemma Int.ne_zero_coe_mul (a b : {x : MyInt // x ≠ 0}) :
    ((a * b : {x : MyInt // x ≠ 0}) : MyInt) = a * b := by
    rfl

lemma Int.ne_zero_mk_mul (a b : MyInt) (ah : a ≠ 0) (bh : b ≠ 0) :
  (⟨a, ah⟩ : {x : MyInt // x ≠ 0}) * (⟨b, bh⟩ : {x : MyInt // x ≠ 0}) = ⟨a * b, mul_ne_zero ah bh⟩ :=
  rfl

/-!

### Definition of `MyPrerat`, the pre-rationals

-/

/-- A "pre-rational" is just a pair of integers, the second one non-zero. -/
abbrev MyPrerat := MyInt × {x : MyInt // x ≠ 0}

namespace MyPrerat

/-!

## The equivalence relation on `MyPrerat`

-/

/-- The equivalence relation on pre-rationals, which we'll quotient out
by to get rationals. -/
def R (x y : MyPrerat) : Prop := x.1 * y.2 = x.2 * y.1

-- Lemma saying what definition of `R` is on ordered pairs
lemma R_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    R (a,b) (c,d) ↔ a * d = b * c := by
    rfl

lemma R_refl : ∀ x, R x x := by
  intro x
  rw [R_def]
  ring

lemma R_symm : ∀ {x y}, R x y → R y x := by
  intro x y hx
  rw [R_def] at *
  linarith

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  intro x y z hxy hyz
  rw [R_def] at *
  suffices x.1 * y.2 * (y.1 * z.2) = x.2 * y.2 * y.1 * z.1 by
    by_cases hy1 : y.1 = 0
    · have : (y.2 : MyInt) ≠ 0 := y.2.prop
      simp_all
    · rw [← mul_left_inj' hy1, ← mul_left_inj' y.2.prop]
      linarith
  rw [hxy, hyz]
  linarith

-- Which one to implement directly IsLeftCancelMul or LeftCancelSemigroup?
-- Neither: implement CancelCommMonoid directly and that provides all the other cancelative properties.
-- It looks like in Mathlib one should directly aim for the most specialized class as that trickles down to the classes that it extends and theorems may use those more general classes to generalize.

-- Why is the following not the definition?
-- `class LeftCancelSemigroup (G : Type*) extends Semigroup G, IsLeftCancelMul G`
-- This is probably from how mathlib grew. An instance of LeftCancelSemigroup provides an instance of IsLeftCancelMul indirectly.

/-
Visualization: implementing a more specialized class will autmatically inherit the child classes

  CancelMonoid
  ├─ LeftCancelMonoid
  │  ├─ Monoid: `npow`, etc...
  │  │  ├─ Semigroup
  │  │  └─ MulOneClass
  │  └─ LeftCancelSemigroup: `mul_left_cancel`, inherits IsLeftCancelMul indirectly
  └─ RightCancelMonoid
    └─ ...

  IsCancelMul
  ├─ IsLeftCancelMul: `mul_left_cancel`
  └─ IsRightCancelMul: `mul_right_cancel`

  CancelCommMonoid, inherits CancelMonoid indirectly
  ├─ CommMonoid
  └─ LeftCancelMonoid

The structure is clearly not a tree, but a graph which locally looks like a tree.
Having no cycles in the graph is important to avoid problems.
-/

instance : CancelCommMonoid { x : MyInt // x ≠ 0 } where
  mul_left_cancel := by
    intro ⟨a, ah⟩ ⟨b, bh⟩ ⟨c, ch⟩ h
    simp [Int.ne_zero_mk_mul] at h
    simp
    cases' h with h h
    · exact h
    · contradiction
-- The following properties can just be inlined here in CancelCommMonoid for convenience
-- instance : CommMonoid { x : MyInt // x ≠ 0 } where
  mul_assoc := by
    intro ⟨a, ah⟩ ⟨b, bh⟩ ⟨c, ch⟩
    simp [Int.ne_zero_mk_mul]
    ring
  one := ⟨1, MyInt.zero_ne_one ∘ symm⟩
  one_mul := by
    intro ⟨a, ah⟩
    change (⟨1, _⟩ : { x : MyInt // x ≠ 0 }) * _ = _
    simp [Int.ne_zero_mk_mul]
  mul_one := by
    intro ⟨a, ah⟩
    change _ * (⟨1, _⟩ : { x : MyInt // x ≠ 0 }) = _
    simp [Int.ne_zero_mk_mul]
  mul_comm := by
    intro ⟨a, ah⟩ ⟨b, bh⟩
    simp [Int.ne_zero_mk_mul]
    ring

#synth Semigroup { x : MyInt // x ≠ 0 }
#synth MulOneClass { x : MyInt // x ≠ 0 }
#synth Monoid { x : MyInt // x ≠ 0 }

#synth CommMagma { x : MyInt // x ≠ 0 }
#synth CommSemigroup { x : MyInt // x ≠ 0 }
#synth CommMonoid { x : MyInt // x ≠ 0 }

#synth LeftCancelSemigroup { x : MyInt // x ≠ 0 }
#synth RightCancelSemigroup { x : MyInt // x ≠ 0 }

#synth CancelMonoid { x : MyInt // x ≠ 0 }
#synth IsCancelMul { x : MyInt // x ≠ 0 }

#synth MulOneClass { x : MyInt // x ≠ 0 }

-- This can't be simp because it goes backward
lemma _root_.MyInt.ne_zero_mk_one_eq_one : (⟨1, one_ne_zero⟩ : { x : MyInt // x ≠ 0 }) = 1 := rfl

@[simp] lemma _root_.MyInt.ne_zero_one_eq_one : ((1 : { x : MyInt // x ≠ 0 }) : MyInt) = 1 := rfl

#check (1 : { x : MyInt // x ≠ 0 })

/-- Enable `≈` notation for `R` and ability to quotient by it. -/
instance R_equiv : Setoid MyPrerat where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

-- Teach the definition of `≈` to the simplifier
@[simp] lemma equiv_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (a, b) ≈ (c, d) ↔ a * d = b * c := by
  rfl

-- Teach the definition of `Setoid.r` to the simplifier
@[simp] lemma equiv_def' (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    Setoid.r (a, b) (c, d) ↔ a * d = b * c := by
  rfl

-- Version without destructuring
@[simp] lemma equiv_def'' (a b : MyPrerat) :
    Setoid.r a b ↔ a.1 * b.2 = a.2 * b.1 := by
  rfl

/-!

## The algebraic structure on the pre-rationals

-/

/-!

# Negation

-/

/-- Negation on pre-rationals. -/
def neg (x : MyPrerat) : MyPrerat := (-x.1, x.2)

-- teach it to the simplifier
@[simp] lemma neg_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) : neg (a, b) = (-a, b) := by
  rfl

lemma neg_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  unfold neg
  rw [equiv_def] at *
  simp only [ne_eq, neg_mul, mul_neg, neg_inj]
  exact h

/-

## Addition

-/

/-- Addition on pre-rationals. -/
def add (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.2 + ab.2 * cd.1, ab.2 * cd.2)

-- teach it to the simplifier
@[simp] lemma add_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    add (a, b) (c, d) = (a * d + b * c, b * d) := by
  rfl

lemma add_comm (x y : MyPrerat) :
    add x y = add y x := by
  simp [add]
  constructor
  · ring
  · rw [mul_comm] -- from CommMonoid

lemma add_quotient₁ ⦃x x' y : MyPrerat⦄ (h : x ≈ x') :
    add x y ≈ add x' y := by
  unfold add
  rw [equiv_def] at *
  rw [mul_add, add_mul]
  have : x.1 * y.2 * ↑(x'.2 * y.2) = x.1 * x'.2 * y.2 * y.2
  · push_cast
    ac_rfl
  rw [this]
  rw [h]
  push_cast
  ac_rfl

lemma add_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') ⦃y y' : MyPrerat⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  have h1 : add x y ≈ add x' y := add_quotient₁ h
  have h2 : add y x' ≈ add y' x' := add_quotient₁ h'
  rw [add_comm y, add_comm y'] at h2
  exact Setoid.trans h1 h2

/-

## Multiplication

-/

/-- Multiplication on pre-rationals. -/
def mul (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.1, ab.2 * cd.2)

-- teach it to the simplifier
@[simp] lemma mul_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    mul (a, b) (c, d) = (a * c, b * d) := by
  rfl


lemma mul_comm (x y : MyPrerat) :
    mul x y = mul y x := by
  simp [mul]
  constructor
  · ring
  · rw [CommMonoid.mul_comm] -- from CommMonoid

lemma mul_quotient₁ ⦃x x' y : MyPrerat⦄ (h : x ≈ x') :
    mul x y ≈ mul x' y := by
  unfold mul
  rw [equiv_def] at *
  have : x.1 * y.1 * ↑(x'.2 * y.2) = (x.1 * x'.2) * y.1 * y.2
  · push_cast
    ac_rfl
  rw [this]
  rw [h]
  push_cast
  ac_rfl

lemma mul_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') ⦃y y' : MyPrerat⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  have h1 := mul_quotient₁ h (y := y)
  have h2 := mul_quotient₁ h' (y := x')
  rw [mul_comm x' y] at h1
  rw [mul_comm y' x'] at h2
  exact Setoid.trans h1 h2

/-

## Reciprocal

-/

/-- Reciprocal, or inverse, on pre-rationals. -/
noncomputable
def inv (x : MyPrerat) : MyPrerat := if ha : x.1 ≠ 0 then ⟨x.2, x.1, ha⟩ else ⟨0, 1, by simp⟩

-- teach it to the simplifier
@[simp] lemma inv_def {a : MyInt} (b : {x : MyInt // x ≠ 0}) (ha : a ≠ 0) :
    inv (a, b) = (b.1, ⟨a, ha⟩) := by
  unfold inv
  simp [ha]

lemma inv_def' (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    inv (a, b) = if ha : a ≠ 0 then ⟨b, a, ha⟩ else ⟨0, 1, by simp⟩ := by
  rfl

lemma inv_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') : inv x ≈ inv x' := by
  unfold inv
  by_cases ha : x.1 = 0
  · have ha' : x'.1 = 0
    · rw [equiv_def] at h
      rw [ha, zero_mul] at h
      simp at h
      have : (x.2 : MyInt) ≠ 0 := Subtype.prop x.2
      simp_all
    simp [ha, ha']
  · have ha' : x'.1 ≠ 0
    · rw [equiv_def] at h
      intro hf
      rw [hf, mul_zero] at h
      simp at h
      cases' h with h h
      · contradiction
      · have : (x'.2 : MyInt) ≠ 0 := Subtype.prop x'.2
        contradiction
    · simp [ha, ha']
      rw [equiv_def] at h
      exact (Eq.symm h)

end MyPrerat

open MyPrerat

/-!

## The rationals: definition and algebraic structure

-/

/-- Make the rationals as a quotient of prerationals. -/
abbrev MyRat := Quotient R_equiv

namespace MyRat

@[simp] lemma Quot_eq_Quotient (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := by
  rfl

-- `0` notation (the equiv class of (0,1))
instance zero : Zero MyRat where zero := ⟦(0, ⟨1, one_ne_zero⟩)⟧

-- lemma stating definition of zero
lemma zero_def : (0 : MyRat) = ⟦(0, ⟨1, one_ne_zero⟩)⟧ := by
  rfl

-- `1` notation (the equiv class of (1,1))
instance one : One MyRat where one := ⟦(1, ⟨1, one_ne_zero⟩)⟧

-- lemma stating definition of one
lemma one_def : (1 : MyRat) = ⟦(1, ⟨1, one_ne_zero⟩)⟧ := by
  rfl

/-- Negation on rationals. -/
def neg : MyRat → MyRat := Quotient.map MyPrerat.neg neg_quotient

-- unary `-` notation
instance : Neg MyRat where neg := neg

@[simp] lemma neg_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    -(⟦(a, b)⟧ : MyRat) = ⟦(-a, b)⟧ := by
  rfl

@[simp] lemma neg_def' (x : MyPrerat) :
    -(⟦x⟧ : MyRat) = ⟦(-x.1, x.2)⟧ := by
  rfl

/-- Addition on integers. -/
def add : MyRat → MyRat → MyRat := Quotient.map₂ MyPrerat.add add_quotient

-- `+` notation
instance : Add MyRat where add := add

lemma add_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) + ⟦(c, d)⟧ = ⟦(a * d + b * c, b * d)⟧ :=
  rfl

/-- Multiplication on integers. -/
def mul : MyRat → MyRat → MyRat  := Quotient.map₂ MyPrerat.mul mul_quotient

-- `*` notation
instance : Mul MyRat where mul := mul

lemma mul_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) * ⟦(c, d)⟧ = ⟦(a * c, b * d)⟧ :=
  rfl

lemma mul_def' (a b : MyPrerat) :
    (⟦a⟧ : MyRat) * ⟦b⟧ = ⟦(a.1 * b.1, a.2 * b.2)⟧ :=
  rfl

/-

## Inverse

-/
/-- reciprocal on nonzero rationals. -/
noncomputable
def inv : MyRat → MyRat := Quotient.map MyPrerat.inv inv_quotient

noncomputable
instance : Inv MyRat := ⟨inv⟩

lemma inv_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat)⁻¹ = ⟦MyPrerat.inv (a, b)⟧ := by
  rfl

/-!

## Tactic hackery

Every single proof of every single ring axiom for the rationals is:
"replace all rationals with pairs of integers, turn the question into a question
about integers, and then get the `ring` tactic to prove it"

The problem is that we need three slightly different tactics depending on whether the
axiom mentions 1, 2 or 3 variables.

-/

section tactic_hackery

-- This section contains everything Kevin knows about tactic writing:
-- you can write a tactic which just does other tactics in some order.

macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    rintro ⟨a, b⟩
    apply Quot.sound
    simp
    try ring)

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    apply Quot.sound
    simp
    try ring)

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    apply Quot.sound
    simp
    try ring)

/-- Tactic for proving equality goals in rings defined as quotients.

It will work if there are between 1 and 3 variables, and it
uses the universal property of quotients to reduce the equality
to an equality of polynomials with coefficients in the *integers*,
and then attempts to use the `ring` tactic to solve it. -/

-- note that we have to go through all this: we can't use `ring`
-- on MyRat directly yet and we're using this tool to prove
-- that it's a commutative ring, after which we will be able to use `ring`.
macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃
  )

end tactic_hackery

instance commRing : CommRing MyRat where
  add := (· + ·)
  add_assoc := by quot_proof
  zero := 0
  zero_add := by quot_proof
  add_zero := by quot_proof
  add_comm := by quot_proof
  mul := (· * ·)
  left_distrib := by quot_proof
  right_distrib := by quot_proof
  zero_mul := by quot_proof
  mul_zero := by quot_proof
  mul_assoc := by quot_proof
  one := 1
  one_mul := by quot_proof
  mul_one := by quot_proof
  neg := (- ·)
  mul_comm := by quot_proof
  neg_add_cancel := by quot_proof
  nsmul := nsmulRec --ignore
  zsmul := zsmulRec --ignore

lemma sub_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) - ⟦(c, d)⟧ = ⟦(a * d - b * c, b * d)⟧ := by
  rw [sub_eq_add_neg]
  simp [neg_def, add_def]
  ring

-- To make the rationals into a field we need to think a little more.

lemma zero_ne_one : (0 : MyRat) ≠ 1 := by
  intro f
  simp [zero_def, one_def] at f

lemma mul_inv_cancel (x : MyRat) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  induction' x using Quotient.inductionOn with r
  cases' r with a b
  rw [zero_def] at hx
  simp at hx
  rw [one_def]
  simp [inv_def, hx, mul_def]
  ring

noncomputable
instance field : Field MyRat where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_inv_cancel := mul_inv_cancel
  inv_zero := by
    simp [zero_def, inv_def, MyPrerat.inv_def']
  qsmul := _ --ignore
  nnqsmul := _ --ignore

/-!

## The natural map from the naturals to the rationals

-/

/-- The natural map from the naturals to the rationals. -/
def i (n : ℕ) : MyRat := ⟦(MyInt.i n, ⟨1, by simp⟩)⟧

-- The natural map preserves 0
lemma i_zero : i 0 = 0 := by
  simp [i, zero_def, MyInt.i, MyInt.zero_def]

-- The natural map preserves 1
lemma i_one : i 1 = 1 := by
  simp [i, one_def, MyInt.i, MyInt.one_def]

-- The natural map preserves addition
lemma i_add (a b : ℕ) : i (a + b) = i a + i b := by
  simp [i, add_def]

-- The natural map preserves multiplication
lemma i_mul (a b : ℕ) : i (a * b) = i a * i b := by
  simp [i, mul_def]

-- The natural map is injective
lemma i_injective : Function.Injective i := by
  intro a b h
  simp [i, MyInt.i] at h
  exact h

/-!

## The natural map from the integers to the rationals

-/

/-- The natural map from the integers to the rationals. -/
def j (n : MyInt) : MyRat := ⟦(n, ⟨1, by simp⟩)⟧

-- The natural map preserves 0
lemma j_zero : j 0 = 0 := by
  simp [j, zero_def]

-- The natural map preserves 1
lemma j_one : j 1 = 1 := by
  simp [j, one_def]

-- The natural map preserves addition
lemma j_add (a b : MyInt) : j (a + b) = j a + j b := by
  simp [j, add_def]

-- The natural map preserves multiplication
lemma j_mul (a b : MyInt) : j (a * b) = j a * j b := by
  simp [j, mul_def]

-- The natural map preserves negation
lemma j_neg (a : MyInt) : j (-a) = -j a := by
  simp [j]

-- The natural map is injective
lemma j_injective (a b : MyInt) : j a = j b ↔ a = b := by
  simp [j]

-- All the proofs were exactly the same as the natural number case.

lemma j_comp_eq_i (n : ℕ) : j (MyInt.i n) = i n := by
  rfl

-- We can now give a formula for `⟦(a, b)⟧` using `j a` and `j b`.

theorem Quotient.mk_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    ⟦(a, b)⟧ = j a * (j b)⁻¹ := by
  simp [j, inv_def, b.prop, mul_def]
  ring

-- Now given a prerational, we never have to unfold it again,
-- because we have got the theorem giving the formula for
-- a general prerational, so we can just rewrite that instead.

-- Simp-normal form removes explicit injections and turns them into casts

@[simp] lemma i_eq_natCast (a : ℕ) : i a = a := by
  induction a <;> simp_all [i_zero, i_one, i_add]

@[simp] lemma j_eq_intCast (a : ℤ) : j a = a := by
  induction a with simp_all [j_zero, j_one, j_add, j_neg, sub_eq_add_neg]

lemma natCast_eq {n : ℕ} : (n : MyRat) = j (MyInt.i n) := by
  rw [← i_eq_natCast]
  simp [i, j]

@[simp] lemma j_natCast_eq {n : ℕ} : j n = (n : MyRat) := by
  rw [← i_eq_natCast]
  simp [i, j]

@[simp] lemma natCast_eq' {n : ℕ} : i n = n := by
  induction n with simp_all

end MyRat

/-!

Want more of this nonsense? See how the concept of order is developed
on the rational numbers in `RationalGameOrder.lean`. It's more
subtle than what we had to do here, which was only equational reasoning.

-/
