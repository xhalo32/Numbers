import Numbers.Reals

import Mathlib.RingTheory.LocalRing.Basic

namespace MyPrereal

def IsPos (x : MyPrereal) : Prop :=
  ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ ≤ x n

open Filter

/-- Filter.Eventually version of IsPos -/
lemma isPos_def' (x : MyPrereal) : IsPos x ↔ ∃ δ, 0 < δ ∧ ∀ᶠ n in atTop, δ ≤ x n := by
  simp only [eventually_atTop]
  rfl

-- lemma pos_of_isPos {x : MyPrereal} (hx : IsPos x) :
--     ∃ N, ∀ n, N ≤ n → 0 < x n := by
--   obtain ⟨δ, δh, N, hN⟩ := hx
--   use N
--   intro n hn
--   specialize hN n hn
--   linarith

-- #check Eventually.mono
-- #check Eventually.mp
-- #check EventuallyLE.trans

lemma eventually_lt_of_le_of_lt {a b c : ℕ → MyRat} (H₁ : ∀ᶠ (n : ℕ) in atTop, a n ≤ b n) (H₂ : ∀ᶠ (n : ℕ) in atTop, b n < c n) : ∀ᶠ (n : ℕ) in atTop, a n < c n :=
  H₂.mp <| H₁.mono fun _ => lt_of_le_of_lt

lemma eventually_lt_of_lt_of_le {a b c : ℕ → MyRat} (H₁ : ∀ᶠ (n : ℕ) in atTop, a n < b n) (H₂ : ∀ᶠ (n : ℕ) in atTop, b n ≤ c n) : ∀ᶠ (n : ℕ) in atTop, a n < c n :=
  H₂.mp <| H₁.mono fun _ => lt_of_lt_of_le

-- lemma pos_of_isPos' {x : MyPrereal} (hx : IsPos x) :
--     ∀ᶠ n in atTop, 0 < x n := by
--   rw [isPos_def'] at hx
--   obtain ⟨δ, δh, hx⟩ := hx
--   apply eventually_lt_of_lt_of_le (eventually_const.mpr δh) hx

@[simp] lemma one_pos : IsPos 1 := by
  refine ⟨1/2, by linarith, 0, ?_⟩
  norm_num

lemma not_isPos_zero {x : MyPrereal} (hx : x ≈ 0) : ¬ IsPos x := by
  simp at *
  unfold IsPos
  push_neg
  intro δ δh N
  specialize hx (δ / 2) (by linarith)
  obtain ⟨M, hM⟩ := hx
  refine ⟨max M N, ?_, ?_⟩
  · exact le_sup_right
  · specialize hM (max M N) le_sup_left
    rw [abs_le] at hM
    linarith

lemma not_isPos_zero' {x : MyPrereal} (hx : (⟦x⟧ : MyReal) = 0) : ¬ IsPos x := by
  rw [MyReal.zero_def, Quotient.eq_iff_equiv] at hx
  exact not_isPos_zero hx

lemma not_equiv_zero_of_isPos {x : MyPrereal} (hx : IsPos x) : ¬(x ≈ 0) := by
  contrapose! hx
  exact not_isPos_zero hx

lemma not_equiv_zero_of_isPos' {x : MyPrereal} (hx : IsPos x) : (⟦x⟧ : MyReal) ≠ 0 := by
  contrapose! hx
  exact not_isPos_zero' hx

lemma isPos_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') (hx : IsPos x) : IsPos x' := by
  simp at h
  unfold IsPos at *
  obtain ⟨δ, δh, N, hN⟩ := hx
  specialize h (δ / 2) (by linarith)
  refine ⟨δ / 2, by linarith, ?_⟩
  obtain ⟨M, hM⟩ := h
  use max M N
  intro n hn
  simp at hn
  specialize hM n hn.1
  specialize hN n hn.2
  rw [abs_le] at hM
  linarith

lemma IsPos.add {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x + y) := by
  unfold IsPos at *
  obtain ⟨δx, δxh, M, hM⟩ := hx
  obtain ⟨δy, δyh, N, hN⟩ := hy
  refine ⟨δx + δy, by linarith, ?_⟩
  use max M N
  intro n hn
  simp at hn
  specialize hM n hn.1
  specialize hN n hn.2
  simp
  grw [hM, hN]

lemma IsPos.mul {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x * y) := by
  unfold IsPos at *
  obtain ⟨δx, δxh, M, hM⟩ := hx
  obtain ⟨δy, δyh, N, hN⟩ := hy
  refine ⟨δx * δy, mul_pos δxh δyh, ?_⟩
  use max M N
  intro n hn
  simp at hn
  specialize hM n hn.1
  specialize hN n hn.2
  simp
  grw [hM, hN]
  linarith

def IsNonneg (x : MyPrereal) : Prop :=
  IsPos x ∨ x ≈ 0

lemma IsNonneg_of_equiv_zero {x : MyPrereal} (hx : x ≈ 0) : IsNonneg x := by
  right
  exact hx

-- Should not be called IsNonneg_of_eventually_nonneg as that would have an ∃ N
lemma IsNonneg_of_nonneg {x : MyPrereal} (N : ℕ) (h : ∀ n, N ≤ n → 0 ≤ x n) : IsNonneg x := by
  unfold IsNonneg
  by_cases hx : x ≈ 0
  · tauto
  · left
    obtain ⟨δ, δh, h2⟩ := pos_of_not_equiv_zero hx
    rw [← eventually_atTop] at h2
    unfold IsPos
    refine ⟨δ, δh, ?_⟩
    rw [← eventually_atTop]
    -- How to apply h inside h2?
    apply Eventually.mp h2
    rw [eventually_atTop]
    use N
    intro n hn δh2
    specialize h n hn
    rw [abs_of_nonneg h] at δh2
    linarith

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  apply IsNonneg_of_nonneg 0
  simp

@[simp]
lemma one_nonneg : IsNonneg 1 := by
  apply IsNonneg_of_nonneg 0
  simp

lemma isNonneg_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') (hx : IsNonneg x) : IsNonneg x' := by
  simp at h
  cases' hx with hx hx
  · left
    obtain ⟨δ, δh, N, hN⟩ := hx
    specialize h (δ / 2) (by linarith)
    obtain ⟨M, hM⟩ := h
    refine ⟨δ / 2, by linarith, max N M, ?_⟩
    intro n hn
    rw [sup_le_iff] at hn
    specialize hN _ hn.1
    specialize hM _ hn.2
    rw [abs_le] at hM
    linarith
  · right
    simp_all
    sorry

-- This should be in mathlib
@[simp] lemma _root_.Filter.not_eventually_atTop_false {α : Type*} [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] : ¬ ∀ᶠ (_ : α) in atTop, False := by
  intro h
  rw [eventually_atTop] at h
  obtain ⟨a, ha⟩ := h
  exact ha a le_rfl

lemma eq_zero_of_isNonneg_of_isNonneg_neg {x : MyPrereal} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x ≈ 0 := by
  rw [IsNonneg, IsPos] at *
  rcases h with h | h <;> rcases h' with h' | h'
  ·
    obtain ⟨δ, δh, h⟩ := h
    obtain ⟨δ', δh', h'⟩ := h'
    rw [← eventually_atTop] at *
    apply eventually_lt_of_lt_of_le (eventually_const.mpr δh) at h
    apply eventually_lt_of_lt_of_le (eventually_const.mpr δh') at h'
    simp only [neg_def'] at h'
    have := h.and h'
    have lt_gt_iff_false (n) : 0 < x n ∧ 0 < -x n ↔ False
    · simp
      intro
      linarith
    simp_rw [lt_gt_iff_false] at this
    apply not_eventually_atTop_false at this
    contradiction
  · simp_all
  · exact h
  · simp_all

lemma isNonneg_neg_of_not_isNonneg {x : MyPrereal} (hx : ¬ IsNonneg x) : IsNonneg (-x) := by
  left
  simp [IsPos]
  unfold IsNonneg IsPos at hx
  push_neg at hx
  obtain ⟨h, hx⟩ := hx
  -- The king of lemmas
  apply pos_of_not_equiv_zero at hx
  obtain ⟨δ, δh, hN⟩ := hx

  -- For all positive delta, x is frequently < δ
  specialize h δ δh
  -- hN: eventually |x n| is outside δ ball
  -- h: frequently x n < δ
  -- therefore it's frequently < -δ

  simp_rw [← eventually_atTop] at hN
  simp_rw [← frequently_atTop] at h
  have both := Eventually.and_frequently hN h
  have _(n) : δ < |x n| ∧ x n < δ ↔ x n < -δ
  ·
    rw [lt_abs]
    constructor
    · rintro ⟨h1 | h1, h2⟩ <;> linarith
    · intro h
      constructor
      · right
        linarith
      · linarith
  simp_rw [this] at both
  simp_rw [frequently_atTop] at both
  obtain ⟨N, hN⟩ := both 0

  -- Now due to convergence, it's not only frequently, it's eventually
  have cauchy := x.2
  unfold IsCauchy at cauchy
  specialize cauchy δ δh
  obtain ⟨M, hM⟩ := cauchy

  refine ⟨δ, δh, max M N, ?_⟩
  intro n hn
  specialize hM (max M N) n sorry (le_of_max_le_left hn)
  -- If N ≥ M then this might hold if δ is tweaked
  sorry

end MyPrereal

open MyPrereal

namespace MyReal

def IsNonneg : MyReal → Prop := Quotient.lift (MyPrereal.IsNonneg) <| fun _ _ h ↦
  propext ⟨fun hx ↦ isNonneg_quotient h hx, fun hy ↦ isNonneg_quotient (symm h) hy⟩

lemma isNonneg_def {x : MyPrereal} : IsNonneg ⟦x⟧ ↔ x.IsNonneg := by
  rfl

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  rw [zero_def, isNonneg_def]
  exact MyPrereal.zero_nonneg

lemma eq_zero_of_isNonneg_of_isNonneg_neg {x : MyReal} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x = 0 := by
  induction' x using Quotient.inductionOn with x
  rw [zero_def, Quotient.eq]
  rw [neg_def] at h'
  rw [isNonneg_def] at *
  exact MyPrereal.eq_zero_of_isNonneg_of_isNonneg_neg h h'

lemma IsNonneg.add {x y : MyReal} (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x + y) := by
  by_cases h : x = 0 ∨ y = 0
  · cases h <;> simp_all
  · simp at h
    induction' x using Quotient.inductionOn with x
    induction' y using Quotient.inductionOn with y
    rw [add_def]
    rw [isNonneg_def] at *
    simp only [zero_def, Quotient.eq] at h
    cases h

    rcases hx with hx | hx <;> rcases hy with hy | hy
    · left
      exact IsPos.add hx hy
    · contradiction
    · contradiction
    · contradiction

lemma IsNonneg.mul {x y : MyReal} (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x * y) := by
  by_cases h : x = 0 ∨ y = 0
  · cases h <;> simp_all
  · simp at h
    induction' x using Quotient.inductionOn with x
    induction' y using Quotient.inductionOn with y
    rw [mul_def]
    rw [isNonneg_def] at *
    simp only [zero_def, Quotient.eq] at h
    cases h

    rcases hx with hx | hx <;> rcases hy with hy | hy
    · left
      exact IsPos.mul hx hy
    · contradiction
    · contradiction
    · contradiction

def le (x y : MyReal) : Prop := IsNonneg (y - x)

instance : LE MyReal where
  le := le

lemma le_def (x y : MyReal) : x ≤ y ↔ IsNonneg (y - x) := by
  rfl

lemma zero_le_iff_isNonneg (x : MyReal) : 0 ≤ x ↔ IsNonneg x := by
  rw [le_def, sub_zero]

lemma zero_le_one : (0 : MyReal) ≤ 1 := by
  rw [le_def, sub_zero]
  exact one_nonneg

lemma le_refl (x : MyReal) : x ≤ x := by
  simp [le_def]

lemma le_trans (x y z : MyReal) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  simp [le_def] at *
  have := IsNonneg.add h1 h2
  simp at this
  exact this

lemma le_antisymm (x y : MyReal) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  simp [le_def] at *
  rw [← sub_eq_zero]
  apply eq_zero_of_isNonneg_of_isNonneg_neg
  · exact hyx
  · simp
    exact hxy

instance partialOrder : PartialOrder MyReal where
  le := (. ≤ .)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

instance : ZeroLEOneClass MyReal := ⟨zero_le_one⟩

-- This is strangely called "def"
lemma pos_def {x : MyPrereal} : IsPos x ↔ 0 < (⟦x⟧ : MyReal) := by
  rw [lt_iff_le_and_ne]
  rw [le_def, sub_zero, ne_eq, zero_def, Quotient.eq]
  rw [isNonneg_def, MyPrereal.IsNonneg]

  constructor
  · intro h
    constructor
    left
    exact h
    have := not_equiv_zero_of_isPos h
    exact (this ∘ Setoid.symm)
  · tauto

lemma add_le_add_left (x y : MyReal) (h : x ≤ y) (t : MyReal) : t + x ≤ t + y := by
  simp [le_def]
  exact h

lemma mul_nonneg (x y : MyReal) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  simp [le_def] at *
  apply IsNonneg.mul hx hy

instance : IsOrderedAddMonoid MyReal where
  add_le_add_left := add_le_add_left

instance : IsOrderedRing MyReal :=
  IsOrderedRing.of_mul_nonneg mul_nonneg

lemma isPos_const_iff {x : MyRat} : IsPos ⟨_, IsCauchy.const x⟩ ↔ 0 < x := by
  simp [IsPos]
  constructor
  · intro h
    choose δ δh N hN using h
    apply lt_of_lt_of_le δh
    exact hN _ le_rfl
  · intro h
    refine ⟨x / 2, by linarith, 0, ?_⟩
    simp
    exact h.le

theorem _root_.MyPrereal.equiv_const {a b : MyRat} : a = b ↔ MyPrereal.R_equiv ⟨_, IsCauchy.const a⟩ ⟨_, IsCauchy.const b⟩ := by
  constructor
  · rintro rfl
    exact R_refl _
  · intro h
    simp at h
    by_contra hab
    specialize h (|a - b| / 2) ?_
    · simp [sub_eq_zero, hab]
    · obtain ⟨N, h⟩ := h
      specialize h _ le_rfl
      rw [le_div_iff₀ (by linarith)] at h
      simp [mul_two, sub_eq_zero] at h
      contradiction

lemma k_le_iff (x y : MyRat) : k x ≤ k y ↔ x ≤ y := by
  by_cases hxy : y = x
  · simp_all
  · simp [k, le_def, sub_def]
    change IsNonneg ⟦⟨fun _ => y - x, _⟩⟧ ↔ _
    rw [isNonneg_def]
    rw [MyPrereal.IsNonneg]
    constructor
    · intro h
      rcases h with h | h
      · rw [isPos_const_iff] at h
        linarith
      · rw [MyPrereal.equiv_const] at hxy
        simp at h
        contradiction
    · intro h
      left
      rw [isPos_const_iff]
      rw [sub_pos]
      exact lt_of_le_of_ne h (hxy ∘ symm)

lemma k_lt_iff (x y : MyRat) : k x < k y ↔ x < y := by
  simp [lt_iff_le_and_ne, k_le_iff, k_injective.ne_iff]

lemma le_total (x y : MyReal) : x ≤ y ∨ y ≤ x := by
  rw [or_iff_not_imp_left] -- ooh finally found this gem
  intro h
  induction' x using Quotient.inductionOn with x
  induction' y using Quotient.inductionOn with y
  rw [le_def, ← neg_sub]
  exact isNonneg_neg_of_not_isNonneg h

noncomputable instance linearOrder : LinearOrder MyReal where
  le_total := le_total
  toDecidableLE := Classical.decRel _

lemma mul_pos (a b : MyReal) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  induction' a using Quotient.inductionOn with a
  induction' b using Quotient.inductionOn with b
  rw [mul_def]
  rw [← pos_def] at *
  exact IsPos.mul ha hb

noncomputable instance strictOrderedRing : IsStrictOrderedRing MyReal :=
  IsStrictOrderedRing.of_mul_pos mul_pos
