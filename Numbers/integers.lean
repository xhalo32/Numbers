import Mathlib.Tactic

/-!

All the original work is by Kevin Buzzard.

# The integers

In this file we assume all standard facts about the naturals, and then build
the integers from scratch.

The strategy is to observe that every integer can be written as `a - b`
for `a` and `b` naturals, so we define the "pre-integers" to be `ℕ × ℕ`, the pairs
`(a, b)` of naturals. We define an equivalence relation `≈` on `ℕ × ℕ`, with the
idea being that `(a, b) ≈ (c, d)` if and only if `a - b = c - d`. This doesn't
make sense yet, but the equivalent equation `a + d = b + c` does. We prove
that this is an equivalence relation, and define the integers to be the quotient.

## The ring structure on the integers

We extend addition and multiplication from the naturals to the integers,
and also define negation `-x` and subtraction `x - y`.
We then prove that the integers are a commutative ring. The proofs are all of
the form "reduce to a question about naturals, and then solve it using tactics
which prove theorems about naturals".

## The ordering on the integers

We prove that the integers are a total order, and also that the ordering
plays well with the ring structure.

-/

/-!

## The pre-integers

-/

-- A term of type `MyPreint` is just a pair of natural numbers.
abbrev MyPreint := ℕ × ℕ

namespace MyPreint

/-!

## The equivalence relation on the pre-integers

-/

/-- The equivalence relation on pre-integers, which we'll quotient out
by to get integers. -/
def R (x y : MyPreint) : Prop := x.1 + y.2 = x.2 + y.1

/-- Useful lemma that is mathematically trivial. -/
lemma R_def (a b c d : ℕ) : R (a,b) (c,d) ↔ a + d = b + c := by
  rfl

lemma R_refl : ∀ x, R x x := by
  intro x
  unfold R
  rw [add_comm]

lemma R_symm : ∀ {x y}, R x y → R y x := by
  intro x y h
  unfold R at *
  rw [add_comm, ←h, add_comm]

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  intro x y z hx hz
  unfold R at *
  suffices x.1 + y.2 + y.1 + z.2 = x.2 + y.1 + y.2 + z.1 by
    linarith
  linarith

/-- Enable `≈` notation for `R` and ability to quotient by it -/
-- you can ignore this
instance R_equiv : Setoid MyPreint where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

-- Teach the definition of `≈` to the simplifier, so `simp` becomes more powerful
@[simp] lemma equiv_def (a b c d : ℕ) : (a, b) ≈ (c, d) ↔ a + d = b + c := by
  rfl

-- Teach the definition of `Setoid.r` to the simplifier, so `simp` becomes more powerful
@[simp] lemma equiv_def' (a b c d : ℕ) : Setoid.r (a, b) (c, d) ↔ a + d = b + c := by
  rfl

-- Variant with MyPreints not destructured to nats
@[simp] lemma equiv_def'' (a b : MyPreint) : Setoid.r a b ↔ a.1 + b.2 = a.2 + b.1 := by
  rfl

/-!

## The algebraic structure on the pre-integers

-/

/-- Negation on pre-integers. -/
def neg (x : MyPreint) : MyPreint := (x.2, x.1)

-- teach it to the simplifier
@[simp] lemma neg_def (a b : ℕ) : neg (a, b) = (b, a) := by
  rfl

lemma neg_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  unfold neg
  -- cases' x with x1 x2
  -- cases' x' with x'1 x'2
  simp
  rw [← h]

/-- Addition on pre-integers. -/
@[simp] def add (x y : MyPreint) : MyPreint := (x.1 + y.1, x.2 + y.2)

-- teach it to the simplifier
@[simp] lemma add_def (a b c d : ℕ) : add (a, b) (c, d) = (a + c, b + d) := by
  rfl

lemma add_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  simp
  suffices y.1 + (x.1 + x'.2) + y'.2 = y.2 + (x.2 + x'.1) + y'.1 by
    linarith
  rw [h]
  suffices y.1 + y'.2 = y.2 + y'.1 by
    linarith
  rw [h']

/-- Multiplication on pre-integers. -/
@[simp] def mul (x y : MyPreint) : MyPreint :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

-- teach it to the simplifier
@[simp] lemma mul_def (a b c d : ℕ) : mul (a, b) (c, d) = (a * c + b * d, a * d + b * c) := by
  rfl

lemma mul_comm (x y : MyPreint) :
    mul x y = mul y x := by
  simp
  constructor <;> ring

lemma mul_quotient' ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y : MyPreint⦄ :
    mul x y ≈ mul x' y := by
  simp
  suffices (x.1 + x'.2) * y.1 + (x.2 + x'.1) * y.2 = (x.1 + x'.2) * y.2 + (x.2 + x'.1) * y.1 by
    linarith
  rw [h]
  ring

lemma mul_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  trans x'.mul y
  apply mul_quotient'
  exact h
  rw [mul_comm, mul_comm x']
  apply mul_quotient'
  exact h'

  -- x.mul y ≈ x'.mul y ≈ x'.mul y'

  -- h
  -- x1 + x'2 = x2 + x'1

  -- h'
  -- y1 + y'2 = y2 + y'1

  -- left side
  --     | x1       | x2
  -------|----------|-------
  --  y1 | x1  y1   |
  --  y2 |          | x2 y2
  --
  --     | x'1      | x'2
  -------|----------|-------
  -- y'1 |          | x'2 y'1
  -- y'2 | x'1 y'2  |


  -- right side
  --     | x1       | x2
  -------|----------|-------
  --  y1 |          | x2  y1
  --  y2 | x1  y1   |
  --
  --     | x'1      | x'2
  -------|----------|-------
  -- y'1 | x'1 y'1  |
  -- y'2 |          | x'2 y'2

  -- x1 y1 + x'2 y'1     (+ x1 y'1 +)
  --

end MyPreint

open MyPreint

/-!

## The integers: definition and algebraic structure -/

/-- Make the integers as a quotient of preintegers. -/
abbrev MyInt := Quotient R_equiv

-- Now one can use the notation `⟦(a,b)⟧` to denote the class of `(a,b)`.

namespace MyInt

@[simp] lemma Quot_eq_Quotient (a b : ℕ) : Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := by
  rfl

-- `0` notation (the equiv class of (0,0))
instance zero : Zero MyInt where zero := ⟦(0, 0)⟧

-- lemma stating definition of zero
lemma zero_def : (0 : MyInt) = ⟦(0, 0)⟧ := by
  rfl

-- `1` notation (the equiv class of (1,0))
instance one : One MyInt where one := ⟦(1, 0)⟧

-- lemma stating definition of one
lemma one_def : (1 : MyInt) = ⟦(1, 0)⟧ := by
  rfl

/-- Negation on integers. -/
def neg : MyInt → MyInt := Quotient.map MyPreint.neg neg_quotient

-- unary `-` notation
instance : Neg MyInt where neg := neg

/-- Addition on integers. -/
def add : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.add add_quotient

-- `+` notation
instance : Add MyInt where add := add

/-- Multiplication on integers. -/
def mul : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.mul mul_quotient

-- `*` notation
instance : Mul MyInt where mul := mul

lemma mul_def (a b c d : ℕ) : (⟦(a, b)⟧ : MyInt) * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ := by
  apply Quot.sound
  simp only [MyPreint.mul]
  exact R_equiv.refl _

lemma add_def (a b c d : ℕ) : (⟦(a, b)⟧ : MyInt) + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧ :=
  rfl

lemma add_assoc : ∀ (x y z : MyInt), (x + y) + z = x + (y + z) := by
  apply Quotient.ind
  intro ⟨a, b⟩
  apply Quotient.ind
  intro ⟨c, d⟩
  apply Quotient.ind
  intro ⟨e, f⟩

  simp [add_def]
  linarith

--The same will happen for almost everything else we want to prove!

/-!

## Tactic hackery

Every single proof of every single ring axiom for the integers is:
"replace all integers with pairs of naturals, turn the question into a question
about naturals, and then get the `ring` tactic to prove it"

One slight problem is that we need three different tactics depending on whether the
axiom mentions 1, 2 or 3 variables. So we write three tactics and then one tactic
which does all three cases.

-/

macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    rintro ⟨a, b⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

/-- Tactic for proving equality goals in rings defined as quotients. -/
macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃)

instance commRing : CommRing MyInt where
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
  nsmul := nsmulRec --ignore this
  zsmul := zsmulRec --ignore this

lemma zero_ne_one : (0 : MyInt) ≠ 1 := by
  intro f
  rw [zero_def, one_def, Quotient.eq, MyPreint.equiv_def'] at f
  contradiction


lemma aux_mul_lemma (a b c d : ℕ) (h : a * d + b * c = a * c + b * d) : a = b ∨ c = d := by
  induction a generalizing b with
  | zero =>
    simp_all
    tauto
  | succ e he =>
    cases b with
    | zero =>
      simp_all
    | succ f =>
      specialize he f
      simp
      apply he
      simp [Nat.succ_mul] at h
      linarith

lemma mul_ne_zero (x y : MyInt) : x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by
  refine Quot.induction_on₂ x y ?_
  intro ⟨a, b⟩ ⟨c, d⟩ ha hc
  simp [zero_def, mul_def] at *
  intro hf
  apply aux_mul_lemma at hf
  tauto

lemma eq_of_mul_eq_mul_right {x y z : MyInt} (hx : x ≠ 0) (h : y * x = z * x) : y = z := by
  revert h hx
  refine Quot.induction_on₃ x y z ?_
  intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ h hMul
  simp at *
  simp [mul_def] at hMul
  simp [zero_def] at h
  suffices  a * (c + f) + b * (d + e) = a * (d + e) + b * (c + f) by
    apply aux_mul_lemma at this
    tauto
  linarith

/-!

## The map from the naturals to the integers

-/

/-- The natural map from the naturals to the integers. -/
def i (n : ℕ) : MyInt := ⟦(n, 0)⟧

-- The natural map preserves 0
@[simp] lemma i_zero : i 0 = 0 := by
  rfl

-- The natural map preserves 1
@[simp] lemma i_one : i 1 = 1 := by
  rfl

-- The natural map preserves addition
@[simp] lemma i_add (a b : ℕ) : i (a + b) = i a + i b := by
  rfl

-- The natural map preserves multiplication
@[simp] lemma i_mul (a b : ℕ) : i (a * b) = i a * i b := by
  unfold i
  rw [mul_def]
  simp only [mul_zero, add_zero, zero_mul]

-- The natural map is injective
lemma i_injective : Function.Injective i := by
  intro x y h
  unfold i at h
  simp only [Quotient.eq, equiv_def', add_zero, zero_add] at h
  exact h

/-!

## Linear order structure on the integers

-/

/-- We say `x ≤ y` if there's some natural `a` such that `y = x + a` -/
def le (x y : MyInt) : Prop := ∃ a : ℕ, y = x + i a

-- Notation `≤` for `le`
instance : LE MyInt where
  le := le

lemma le_refl (x : MyInt) : x ≤ x := by
  use 0
  rw [left_eq_add]
  exact i_zero

lemma le_trans (x y z : MyInt) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  obtain ⟨a, ah⟩ := h1
  obtain ⟨b, bh⟩ := h2
  use (a + b)
  rw [i_add, ← add_assoc, ← ah]
  exact bh

lemma le_antisymm (x y : MyInt) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  obtain ⟨a, ah⟩ := hxy
  obtain ⟨b, bh⟩ := hyx
  rw [ah] at bh
  rw [add_assoc, ← i_add, left_eq_add, ← i_zero] at bh
  apply i_injective at bh
  have : a = 0 ∧ b = 0 := by
    exact Nat.eq_zero_of_add_eq_zero bh
  rw [this.1, i_zero, add_zero] at ah
  exact ah.symm

lemma le_total (x y : MyInt) : x ≤ y ∨ y ≤ x := by
  by_cases h : x ≤ y
  · left
    exact h
  · right
    by_contra hf
    change ¬ le x y at h
    change ¬ le y x at hf
    unfold le at *
    push_neg at *

    revert hf h
    refine Quot.induction_on₂ x y ?_
    intro ⟨a, b⟩ ⟨c, d⟩ ha hc
    unfold i at *
    simp_all
    simp_rw [add_def, add_zero] at *
    simp [Quotient.eq] at *
    convert_to ∀ z, a + d ≠ (c + b) + z at ha; ring_nf
    convert_to ∀ z, c + b ≠ (a + d) + z at hc; ring_nf
    by_cases hle : a + d ≤ c + b
    · rw [le_iff_exists_add] at hle
      obtain ⟨z, hz⟩ := hle
      tauto
    · by_cases hle' : c + b ≤ a + d
      · rw [le_iff_exists_add] at hle'
        obtain ⟨z, hz⟩ := hle'
        tauto
      · linarith

    -- have (x y : MyInt) : x ≠ y → ¬ x ≤ y ∨ ¬ y ≤ x
    -- · intro h
    --   refine not_and_or.mp ?_
    --   intro hf
    --   have := le_antisymm _ _ hf.1 hf.2
    --   contradiction


    -- have gona (a) := this y (x + i a) (h a)
    -- simp at gona
    -- have (x y) (hxy) := (le_antisymm x y hxy).mt

noncomputable instance linearOrder : LinearOrder MyInt where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  le_total := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable _ --ignore this

lemma zero_le_one : (0 : MyInt) ≤ 1 := by
  use 1
  rw [i_one]
  rfl

/-- The natural map from the naturals to the integers preserves and reflects `≤`. -/
lemma i_le_iff (a b : ℕ) : i a ≤ i b ↔ a ≤ b := by
  constructor
  · intro h
    unfold i at *
    obtain ⟨c, hc⟩ := h
    unfold i at hc
    rw [add_def, add_zero] at hc
    simp at hc
    linarith
  · intro h
    use (b  - a)
    unfold i
    rw [add_def, add_zero]
    simp
    exact Eq.symm (Nat.add_sub_of_le h)

/-

## Interaction between ordering and algebraic structure

-/

lemma add_le_add_left (x y : MyInt) (h : x ≤ y) (z : MyInt) : z + x ≤ z + y := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [hn]
  ring

lemma mul_pos (x y : MyInt) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  revert hx hy
  refine Quot.induction_on₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩
  simp
  intro hx hy
  rw [mul_def]
  change 0 ≤ _ ∧ ¬ _ ≤ 0
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only at *
  have pos : 0 ≤ (⟦(a * c + b * d, a * d + b * c)⟧ : MyInt)
  · rw [zero_def] at *
    obtain ⟨n, hn⟩ := hx1
    obtain ⟨m, hm⟩ := hy1
    use (n * m)
    unfold i at *
    rw [add_def, zero_add, add_zero] at *
    simp at *
    rw [hn, hm]
    ring
  refine ⟨pos, ?_⟩
  rw [zero_def] at *
  change ¬ le _ _ at hx2
  change ¬ le _ _ at hy2
  unfold le at *
  push_neg at *
  unfold i at *
  simp [add_def] at *
  -- a * d ≥ a * c ↔ d ≥ c
  -- b * d ≥ b * c ↔ d ≥ c
  by_cases h : d ≥ c
  ·
    have ha : a * d ≥ a * c := Nat.mul_le_mul_left _ h
    have hb : b * d ≥ b * c := Nat.mul_le_mul_left _ h
    apply lt_of_le_of_ne pos
    simp at *
    intro hf
    have : a * (d - c) = b * (d - c)
    · rw [Nat.mul_sub, Nat.mul_sub]
      suffices a * d - a * c + a * c + b * c = b * d - b * c + b * c + a * c by
        linarith
      rw [Nat.sub_add_cancel hb, Nat.sub_add_cancel ha]
      linarith
    simp at this
    cases' this with t1 t2
    · specialize hx2 0
      simp_all
    · have : d - c + c = 0 + c := by
        exact congrFun (congrArg HAdd.hAdd t2) _
      rw [Nat.sub_add_cancel h, zero_add] at this
      specialize hy2 0
      simp_all
  ·
    simp at h
    apply le_of_lt at h
    have ha : a * d ≤ a * c := Nat.mul_le_mul_left _ h
    have hb : b * d ≤ b * c := Nat.mul_le_mul_left _ h
    apply lt_of_le_of_ne pos
    simp at *
    intro hf
    have : a * (c - d) = b * (c - d)
    · rw [Nat.mul_sub, Nat.mul_sub]
      suffices a * c - a * d + a * d + b * d = b * c - b * d + b * d + a * d by
        linarith
      rw [Nat.sub_add_cancel hb, Nat.sub_add_cancel ha]
      linarith
    simp at this
    cases' this with t1 t2
    · specialize hx2 0
      simp_all
    · have : c - d + d = 0 + d := by
        exact congrFun (congrArg HAdd.hAdd t2) _
      rw [Nat.sub_add_cancel h, zero_add] at this
      specialize hy2 0
      simp_all



lemma mul_nonneg (x y : MyInt) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  obtain ⟨a, hx⟩ := hx
  obtain ⟨b, hy⟩ := hy
  use a * b
  simp_all

#check Left.mul_nonneg

-- This would be useful to get above for MyInt
-- instance : PosMulMono MyInt where
--   elim := by
--     intro a b c hbc
--     simp

instance : Nontrivial MyInt := ⟨0, 1, zero_ne_one⟩

instance : ZeroLEOneClass MyInt := ⟨zero_le_one⟩

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := add_le_add_left

instance : IsStrictOrderedRing MyInt :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma archimedean (x : MyInt) : ∃ (n : ℕ), x ≤ i n := by
  induction' x using Quotient.inductionOn with n
  obtain ⟨a, b⟩ := n
  unfold i
  by_cases h : a ≤ b
  · use 0
    change le _ _
    simp [le, i, add_def]
    use (b - a)
    simp_all
  · use (a - b)
    change le _ _
    simp [le, i, add_def]
    use 0
    simp at h
    apply le_of_lt at h
    simp_all

-- Extra useful instances and stuff

-- This is false if b = 0
-- instance : IsRightCancelMul MyInt where
--   mul_right_cancel := by
--     intro a b c h
--     induction' a using Quotient.inductionOn with a
--     induction' b using Quotient.inductionOn with b
--     induction' c using Quotient.inductionOn with c
--     rw [mul_def, mul_def] at h
--     have h2 := h
--     simp at h
--     simp
--     ring_nf at h
--     have h : b.1 * (a.1 + c.2) + b.2 * (a.2 + c.1)
--            = b.1 * (a.2 + c.1) + b.2 * (a.1 + c.2)
--     · linarith

--     -- we want to eliminate the terms a1 b1, a2 b2, a1 b2, a2 b1
--     -- have : ⟦(a.1 * b.1 + a.2 * b.2,                         a.1 * b.2 + a.2 * b.1)⟧
--     --      = ⟦(a.1 * b.1 + a.2 * b.2 + b.1 * c.2 + b.2 * c.1, a.1 * b.2 + a.2 * b.1 + b.1 * c.2 + b.2 * c.1)⟧
--     -- · simp
--     --   ring
--     -- rw [this] at h2

--     have : ⟦(c.1 * b.1 + c.2 * b.2,                         c.1 * b.2 + c.2 * b.1)⟧
--          = ⟦(c.1 * b.1 + c.2 * b.2 + b.1 * c.2 + b.2 * c.1, c.1 * b.2 + c.2 * b.1 + b.1 * c.2 + b.2 * c.1)⟧
--     · simp
--       ring
--     rw [this] at h2



--     simp at h2
--     ring_nf at h2

--     suffices (a.1 + c.2) * (b.1 + b.2)
--            = (a.2 + c.1) * (b.1 + b.2) by
--       rw [Nat.mul_right_cancel_iff] at this
--       exact this


    -- have h2 : a.1 * (b.1 + c.2) + a.2 * (b.2 + c.1) + b.1 * c.2 + b.2 * c.1
            -- = a.1 * (b.2 + c.2) + a.2 * (b.1 + c.1) + b.1 * c.1 + b.2 * c.2
    -- · linarith


    -- add b1 * (a1 + c1)
    -- suffices b.1 * (a.1 + c.2) = b.1 * (a.2 + c.1)

-- Extra useful lemmas

#synth AddMonoidWithOne MyInt
#check commRing.toAddGroupWithOne.toNatCast

@[simp] lemma i_eq_natCast (a : ℕ) : MyInt.i a = ↑a := by
  induction a <;> simp_all

lemma one_le_of_zero_lt (x : MyInt) (h : 0 < x) : 1 ≤ x := by
  induction' x using Quotient.inductionOn with x
  simp_all [zero_def, one_def]
  rw [lt_iff_le_and_ne] at h
  obtain ⟨⟨n, hn⟩, h2⟩ := h
  simp [i, add_def] at hn
  cases' n with n
  · simp at hn
    have : 0 = (⟦(x.1, x.2)⟧ : MyInt)
    · simp [hn, zero_def]
    contradiction
  · use n
    simp [i, add_def, hn]
    ring

end MyInt
