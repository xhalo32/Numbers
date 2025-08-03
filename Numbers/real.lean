import Numbers.rationals_order

-- Lean already knows the absolute value (since there is an order on `MyRat`: `|x|` is defined as
-- `max (x, -x)`.
--See the files `Mathlib.Algebra.Order.*.Abs` for various properties
abbrev IsCauchy (x : ℕ → MyRat) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε

-- Thanks Kalle for this hint
lemma exists_forall_abs_initial_le (x : ℕ → MyRat) (m : ℕ) : ∃ (M : MyRat), ∀ n < m, |x n| ≤ M := by
  induction' m with m ih
  · use 0
    intro n hn
    contradiction
  · obtain ⟨M, hM⟩ := ih
    use max M |x m|
    intro n hn
    by_cases h : n = m
    · rw [h]
      exact le_sup_right
    · specialize hM n
      have gona : n < m := by
        suffices n ≤ m by
          exact Nat.lt_of_le_of_ne this h
        linarith
      specialize hM gona
      exact le_sup_of_le_left hM

open Finset in
lemma IsCauchy.bounded {x : ℕ → MyRat} (hx : IsCauchy x) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B := by
  unfold IsCauchy at hx
  -- For arbitrary choice of ε we get an N for whict the tail is bounded.
  -- Then we just nead the finite head to be bounded and for that we can use exists_forall_abs_initial_le.
  -- The bound for the tail is chosen to be |x N| + 1, as we can "center" the tail around x N.

  -- One could skolemize hx
  -- choose f hx using hx
  -- let N := f 1

  specialize hx 1 (by linarith)
  obtain ⟨N, hN⟩ := hx

  obtain ⟨M, hM⟩ := exists_forall_abs_initial_le x N

  refine ⟨max (|x N| + 1) M, ?_, ?_⟩
  · apply lt_sup_of_lt_left
    suffices 0 ≤ |x N| by
      linarith
    exact abs_nonneg (x N)
  · intro n
    by_cases hn : n < N
    · exact le_sup_of_le_right (hM _ hn)
    · specialize hN N n
      simp_all
      left
      suffices |x n| - |x N| ≤ 1 by
        linarith
      apply le_trans (abs_sub_abs_le_abs_sub _ _)
      rw [abs_sub_comm]
      exact hN

abbrev MyPrereal := {x // IsCauchy x}

namespace MyPrereal

open MyPrereal

#check FunLike
#check DFunLike

--ignore the following
instance funLike : FunLike MyPrereal ℕ MyRat where
  coe := Subtype.val
  coe_injective' _ _ := Subtype.ext

lemma prop (x : MyPrereal) : ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε :=
  x.2

@[simp] lemma coe_apply {x : ℕ → MyRat} (hx : IsCauchy x) (n : ℕ) :
    (⟨x, hx⟩ : MyPrereal) n = x n := by
  rfl

-- Which way should this go?
-- @[simp]
lemma coe_apply' {x : MyPrereal} (n : ℕ) :
    x n = x.1 n := by
  rfl

lemma bounded (x : MyPrereal) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B :=
  x.2.bounded

def R (x y : MyPrereal) : Prop := ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε

lemma R_def (x y : MyPrereal) : R x y ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  rfl

lemma R_refl : ∀ x, R x x := by
  intro x
  rw [R_def]
  intro ε εh
  use 0
  simp
  exact εh.le

lemma R_symm : ∀ {x y}, R x y → R y x := by
  intro x y
  simp [R_def]
  simp_rw [abs_sub_comm]
  exact id

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  intro x y z h1 h2
  simp [R_def] at *
  intro ε εh
  specialize h1 (ε/2) (by linarith)
  specialize h2 (ε/2) (by linarith)
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use max a b
  intro n nh
  rw [sup_le_iff] at nh
  specialize ha n nh.1
  specialize hb n nh.2
  rw [show ε = ε/2 + ε/2 by linarith]
  nth_grw 1 [← ha]
  grw [← hb]
  apply abs_sub_le

instance R_equiv : Setoid MyPrereal where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

@[simp] lemma equiv_def (x y : MyPrereal) : x ≈ y ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  rfl

@[simp] lemma equiv_def' (x y : MyPrereal) : Setoid.r x y ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  rfl

lemma IsCauchy.const (x : MyRat) : IsCauchy (fun _ ↦ x) := by
  intro ε εh
  use 1
  intros
  simp
  exact εh.le

instance zero : Zero MyPrereal where
  zero := ⟨0, IsCauchy.const 0⟩

@[simp] lemma zero_def (n : ℕ) : (0 : MyPrereal) n = 0 := by
  rfl

instance one : One MyPrereal where
  one := ⟨1, IsCauchy.const 1⟩

@[simp] lemma one_def (n : ℕ) : (1 : MyPrereal) n = 1 := by
  rfl

lemma IsCauchy.neg {x : ℕ → MyRat} (hx : IsCauchy x) : IsCauchy (-x) := by
  rw [IsCauchy] at *
  refine forall_imp (fun ε => forall_imp (fun εh => Exists.imp (fun N => forall_imp (fun p => forall_imp (fun q => forall_imp (fun ph => forall_imp (fun qh => ?_))))))) hx
  intro hx
  rw [abs_sub_comm]
  norm_num
  rw [add_comm, ← sub_eq_add_neg]
  exact hx

instance : Neg MyPrereal where
  neg x := ⟨-x, x.2.neg⟩

@[simp] lemma neg_def (x : ℕ → MyRat) (hx : IsCauchy x) : (-(⟨x, hx⟩ : MyPrereal)) = ⟨-x, hx.neg⟩ := by
  rfl

@[simp] lemma neg_def' (x : MyPrereal) (n : ℕ) : (-x) n = -x n := by
  rfl

lemma neg_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') : -x ≈ -x' := by
  simp at *
  refine forall_imp (fun ε => forall_imp (fun εh => Exists.imp (fun N => forall_imp (fun n => forall_imp (fun hn => ?_))))) h
  intro h
  cases' x with x hx
  cases' x' with x' hx'
  simp at *
  rw [add_comm, ← sub_eq_add_neg, abs_sub_comm]
  exact h

lemma IsCauchy.add {x y : ℕ → MyRat} (hx : IsCauchy x) (hy : IsCauchy y) : IsCauchy (x + y) := by
  simp [IsCauchy] at *
  intro ε εh
  specialize hx (ε/2) (by linarith)
  specialize hy (ε/2) (by linarith)
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use max a b
  intro p q hp hq
  specialize ha p q (le_of_max_le_left hp) (le_of_max_le_left hq)
  specialize hb p q (le_of_max_le_right hp) (le_of_max_le_right hq)
  rw [show ε = ε/2 + ε/2 by linarith]
  nth_grw 1 [← ha]
  grw [← hb]
  rw [show |x p + y p - (x q + y q)| = |x p - x q + (y p - y q)| by ring_nf]
  apply abs_add_le

instance : Add MyPrereal where
  add x y := ⟨x + y, x.2.add y.2⟩

instance : Sub MyPrereal where
  sub x y := x + -y

@[simp] lemma add_def (x y : MyPrereal) (n : ℕ) : (x + y) n = x n + y n := by
  rfl

@[simp] lemma add_def' (x y : MyPrereal) (n : ℕ) : (x + y).val n = x n + y n := by
  rfl

@[simp] lemma sub_def (x y : MyPrereal) (n : ℕ) : (x - y) n = x n - y n := by
  rfl

@[simp] lemma sub_def' (x y : MyPrereal) (n : ℕ) : (x - y).val n = x n - y n := by
  rfl

lemma add_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') ⦃y y' : MyPrereal⦄ (h' : y ≈ y') :
    x + y ≈ x' + y' := by
  simp at *
  intro ε εh
  specialize h  (ε/2) (by linarith)
  specialize h' (ε/2) (by linarith)
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  use max a b
  intro n hn
  specialize ha n (le_of_max_le_left hn)
  specialize hb n (le_of_max_le_right hn)
  rw [show ε = ε/2 + ε/2 by linarith]
  nth_grw 1 [← ha]
  grw [← hb]
  calc _ = |x n - x' n + (y n - y' n)| := by ring_nf
       _ ≤ _                           := by apply abs_add_le

lemma IsCauchy.mul {x y : ℕ → MyRat} (hx : IsCauchy x) (hy : IsCauchy y) : IsCauchy (x * y) := by
  -- A cauchy sequence is bounded, so let's get the bounds of x and y
  obtain ⟨Bx, hBx⟩ := hx.bounded
  obtain ⟨By, hBy⟩ := hy.bounded
  simp [IsCauchy] at *
  intro ε εh

  specialize hx (ε / 2 / (max Bx By)) (div_pos (by linarith) (lt_sup_of_lt_left hBx.1))
  specialize hy (ε / 2 / (max Bx By)) (div_pos (by linarith) (lt_sup_of_lt_left hBx.1))
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy

  use max a b
  intro p q hp hq
  specialize ha p q (le_of_max_le_left hp) (le_of_max_le_left hq)
  specialize hb p q (le_of_max_le_right hp) (le_of_max_le_right hq)

  -- Let's try to convert `x p * y p - x q * y q` to something that involves `x p - x q` and `y p - y q`:
  -- `x p * y p - x q * y q`
  -- `= (x p - x q) * (y p + y q) + x q * y p - x p * y q`
  -- `= y p * (x p - x q) + (x p - x q) * y q + x q * y p - x p * y q`
  -- `= y p * (x p - x q) + x q * y p - x q * y q`
  -- `= y p * (x p - x q) + x q * (y p - y q)`

  have eq : x p * y p - x q * y q = y p * (x p - x q) + x q * (y p - y q)
  · ring
  rw [eq]

  apply le_trans (abs_add_le _ _)
  simp [abs_mul]

  have yp_le : |y p| ≤ max Bx By
  · rw [le_max_iff]
    right
    simp_all
  have xq_le : |x q| ≤ max Bx By
  · rw [le_max_iff]
    left
    simp_all

  grw [yp_le, xq_le]
  rw [← mul_add, mul_comm, ← le_div_iff₀]
  · grw [ha, hb]
    rw [← add_div]
    simp
  · exact lt_sup_of_lt_left hBx.1

instance : Mul MyPrereal where
  mul x y := ⟨x * y, x.2.mul y.2⟩

@[simp] lemma mul_def (x y : MyPrereal) (n : ℕ) : (x * y) n = x n * y n := by
  rfl

@[simp] lemma mul_def' (x y : MyPrereal) (n : ℕ) : (x * y).val n = x n * y n := by
  rfl

lemma mul_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') ⦃y y' : MyPrereal⦄ (h' : y ≈ y') :
    x * y ≈ x' * y' := by
  obtain ⟨Bx, hBx⟩ := x.2.bounded
  obtain ⟨By', hBy'⟩ := y'.2.bounded
  simp at *
  intro ε εh

  let B := max Bx By'
  have hB : 0 < B
  · simp_all only [lt_sup_iff, or_self, B]

  specialize h (ε / 2 / B) (div_pos (by linarith) hB)
  specialize h' (ε / 2 / B) (div_pos (by linarith) hB)
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'

  use max a b
  intro n hn
  specialize ha n (le_of_max_le_left hn)
  specialize hb n (le_of_max_le_right hn)

  simp [← coe_apply'] at *
  -- The factoring to differences has factors y' n and x n, so we use B = max Bx By'
  have eq : x n * y n - x' n * y' n = y' n * (x n - x' n) + x n * (y n - y' n)
  · ring
  rw [eq]

  apply le_trans (abs_add_le _ _)
  simp [abs_mul]

  have xq_le : |x n| ≤ B
  · rw [le_max_iff]
    left
    simp_all
  have yp_le : |y' n| ≤ B
  · rw [le_max_iff]
    right
    simp_all

  grw [yp_le, xq_le]
  rw [← mul_add, mul_comm, ← le_div_iff₀]
  · grw [ha, hb]
    rw [← add_div]
    simp
  · exact lt_sup_of_lt_left hBx.1

/-- This lemma helps us get a statement that eventually x n ≠ 0 for any n

TODO: show converse
-/
lemma pos_of_not_equiv_zero {x : MyPrereal} (H : ¬(x ≈ 0)) :
    ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ < |x n| := by
  simp only [equiv_def, zero_def, sub_zero] at H
  push_neg at H
  obtain ⟨ε, εh, h⟩ := H

  refine ⟨ε/2, by linarith, ?_⟩
  choose f h1 h2 using h
  obtain ⟨N, cauchy⟩ := x.2 (ε/2) (by linarith)
  simp only [← coe_apply'] at *
  use f N
  intro n hn
  specialize cauchy n (f N) (le_trans (h1 N) hn) (h1 N)
  specialize h2 N
  rw [lt_abs] at h2
  rcases h2 with h2 | h2
  · -- x (f N) is positive, and x n is close to it
    rw [lt_abs]
    left
    rw [abs_le'] at cauchy
    simp at cauchy
    linarith
  · -- x (f N) is negative, and x n is close to it
    rw [lt_abs]
    right
    rw [abs_le'] at cauchy
    simp at cauchy
    linarith

lemma IsCauchy.inv {x : MyPrereal} (H : ¬(x ≈ 0)) : IsCauchy (x⁻¹) := by
  obtain ⟨δ, δh, h⟩ := pos_of_not_equiv_zero H
  rw [IsCauchy]
  simp

  intro ε εh
  obtain ⟨N, hN⟩ := h
  obtain ⟨M, hM⟩ := x.2 (ε * (δ * δ)) (mul_pos εh (mul_pos δh δh))

  use max N M
  intro p q hp hq
  have xph := hN p (le_of_max_le_left hp)
  have xqh := hN q (le_of_max_le_left hq)
  specialize hM p q (le_of_max_le_right hp) (le_of_max_le_right hq)
  simp only [← coe_apply'] at *

  by_cases eq : 0 = |x q * x p|
  · rw [abs_mul] at eq
    simp at eq
    rcases eq with eq | eq
    · rw [eq] at xqh
      rw [abs_zero] at xqh
      linarith
    · rw [eq] at xph
      rw [abs_zero] at xph
      linarith
  ·
    simp [abs_mul] at eq
    rw [abs_sub_comm, inv_sub_inv eq.1 eq.2, abs_div, div_le_iff₀, mul_comm (x q)]
    · have : δ * δ < |x p * x q|
      · rw [abs_mul]
        apply mul_lt_mul xph xqh.le δh
        exact abs_nonneg _
      ·
        grw [hM]
        exact mul_le_mul le_rfl this.le (mul_pos δh δh).le εh.le
    · rw [abs_pos]
      exact mul_ne_zero eq.1 eq.2

open Classical in
noncomputable def inv (x : MyPrereal) : MyPrereal := if H : ¬(x ≈ 0) then ⟨_, IsCauchy.inv H⟩ else 0

@[simp] lemma inv_def {x : MyPrereal} (H : ¬(x ≈ 0)) (n : ℕ) :
    inv x n = (x n)⁻¹ := by
  unfold inv
  simp [H]

@[simp] lemma inv_def' {x : MyPrereal} (H : ¬(x ≈ 0)) (n : ℕ) :
    (⟨x⁻¹, IsCauchy.inv H⟩ : MyPrereal) n = (x n)⁻¹ := by
  rfl

lemma inv_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') : inv x ≈ inv x' := by
  by_cases hx : x ≈ 0
  · have hx' : x' ≈ 0
    · symm at h
      exact Setoid.trans h hx
    simp [inv, hx, hx']
  · have hx' : ¬ x' ≈ 0
    · intro hx'
      apply hx
      exact Setoid.trans h hx'
    simp [inv, hx, hx']

    intro ε εh
    obtain ⟨δx, δxh, N, hN⟩ := pos_of_not_equiv_zero hx
    obtain ⟨δx', δxh', M, hM⟩ := pos_of_not_equiv_zero hx'

    specialize h (ε * (δx * δx')) (mul_pos εh (mul_pos δxh δxh'))
    obtain ⟨a, ha⟩ := h

    use max a (max N M)
    intro n hn
    specialize ha n (le_of_max_le_left hn)
    specialize hN n (le_of_max_le_left (le_of_max_le_right hn))
    specialize hM n (le_of_max_le_right (le_of_max_le_right hn))

    by_cases eq : 0 = |x n * x' n|
    · rw [abs_mul] at eq
      simp at eq
      rcases eq with eq | eq
      · rw [eq] at hN
        rw [abs_zero] at hN
        linarith
      · rw [eq] at hM
        rw [abs_zero] at hM
        linarith
    ·
      simp [abs_mul] at eq
      rw [abs_sub_comm, inv_sub_inv eq.2 eq.1, abs_div, div_le_iff₀, mul_comm (x' n)]
      · have : δx * δx' < |x n * x' n|
        · rw [abs_mul]
          apply mul_lt_mul hN hM.le δxh'
          exact abs_nonneg _
        ·
          grw [ha]
          exact mul_le_mul le_rfl this.le (mul_pos δxh δxh').le εh.le
      · rw [abs_pos]
        exact mul_ne_zero eq.2 eq.1

lemma IsCauchy.sub {f g : ℕ → MyRat} (hf : IsCauchy f) (hg : IsCauchy g) : IsCauchy (f - g) := by
  rw [sub_eq_add_neg]
  apply add hf
  exact neg hg

@[simp] lemma sub_def'' {f g : ℕ → MyRat} (hf : IsCauchy f) (hg : IsCauchy g) : (⟨fun n => f n, hf⟩ : MyPrereal) - ⟨fun n => g n, hg⟩ = ⟨fun n => f n - g n, IsCauchy.sub hf hg⟩ := by
  rfl

end MyPrereal

open MyPrereal

abbrev MyReal := Quotient R_equiv

namespace MyReal

@[simp] lemma Quot_eq_Quotient (x : MyPrereal) : Quot.mk Setoid.r x = ⟦x⟧ := by
  rfl

instance zero : Zero MyReal where
  zero := ⟦0⟧

lemma zero_def : (0 : MyReal) = ⟦0⟧ := by
  rfl

instance one : One MyReal where
  one := ⟦1⟧

lemma one_def : (1 : MyReal) = ⟦1⟧ := by
  rfl

def neg : MyReal → MyReal := Quotient.map _ neg_quotient

instance : Neg MyReal where
  neg := neg

lemma neg_def (x : MyPrereal) : -(⟦x⟧ : MyReal) = ⟦-x⟧ := by
  rfl

def add : MyReal → MyReal → MyReal  := Quotient.map₂ _ add_quotient

instance : Add MyReal
  where add := add

lemma add_def (x y : MyPrereal) : (⟦x⟧ : MyReal) + (⟦y⟧ : MyReal) = ⟦x + y⟧ := by
  rfl

def mul : MyReal → MyReal → MyReal  := Quotient.map₂ _ mul_quotient

instance : Mul MyReal where
  mul := mul

lemma mul_def (x y : MyPrereal) : (⟦x⟧ : MyReal) * (⟦y⟧ : MyReal) = ⟦x * y⟧ := by
  rfl

noncomputable
def inv : MyReal → MyReal := Quotient.map _ inv_quotient

noncomputable
instance : Inv MyReal := ⟨inv⟩

lemma inv_def (x : MyPrereal) :
    (⟦x⟧ : MyReal)⁻¹ = ⟦MyPrereal.inv x⟧ := by
  rfl

macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    intro a
    apply Quot.sound
    simp
    intro ε hε
    use 0
    intro n hn
    try {ring_nf; simp [hε.le]})

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    intro a b
    apply Quot.sound
    simp
    intro ε hε
    use 0
    intro n hn
    try {ring_nf; simp [hε.le]})

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    intro a b c
    apply Quot.sound
    simp
    intro ε hε
    use 0
    intro n hn
    try { ring_nf; simp [hε.le] })

macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃)

instance commRing : CommRing MyReal where
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
  nsmul := nsmulRec
  zsmul := zsmulRec

lemma sub_def (x y : MyPrereal) : (⟦x⟧ : MyReal) - (⟦y⟧ : MyReal) = ⟦x - y⟧ := by
  rfl

lemma zero_ne_one : (0 : MyReal) ≠ 1 := by
  simp only [zero_def, one_def, ne_eq, Quotient.eq, equiv_def', MyPrereal.zero_def,
    MyPrereal.one_def]
  push_neg
  refine ⟨1/2, by linarith, ?_⟩
  intro N
  use N
  norm_num

lemma mul_inv_cancel (x : MyReal) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  induction' x using Quotient.inductionOn with x
  rw [zero_def, ne_eq, Quotient.eq_iff_equiv] at hx
  obtain ⟨δ, δh, N, hN⟩ := pos_of_not_equiv_zero hx

  rw [inv_def, mul_def, one_def]
  simp
  intro ε εh
  use N
  intro n hn
  have : x n ≠ 0
  · specialize hN n hn
    rw [← abs_pos]
    linarith
  simp [MyPrereal.inv, hx]
  rw [MyRat.mul_inv_cancel _ this]
  simp
  exact εh.le

noncomputable
instance field : Field MyReal where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_inv_cancel := mul_inv_cancel
  inv_zero := by
    apply Quot.sound
    simp only [MyPrereal.inv, Setoid.refl, not_true_eq_false, reduceDIte, equiv_def',
      MyPrereal.zero_def, sub_self, abs_zero]
    intro ε hε
    exact ⟨0, fun _ _ ↦ hε.le⟩
  qsmul := _
  nnqsmul := _

def k (x : MyRat) : MyReal := ⟦⟨_, IsCauchy.const x⟩⟧

@[simp] lemma k_zero : k 0 = 0 := by
  rfl

@[simp] lemma k_one : k 1 = 1 := by
  rfl

@[simp] lemma k_neg (x : MyRat) : k (-x) = -(k x) := by
  rfl

lemma k_add (x y : MyRat) : k (x + y) = k x + k y := by
  simp only [k, add_def]
  simp
  intros
  use 0
  intros
  linarith

lemma k_sub (x y : MyRat) : k (x - y) = k x - k y := by
  simp only [k, sub_def]
  simp

lemma k_mul (x y : MyRat) : k (x * y) = k x * k y := by
  simp only [k, mul_def]
  simp
  intros
  use 0
  intros
  linarith

lemma k_injective : Function.Injective k := by
  intro x y h
  simp [k] at h
  by_contra hf
  apply sub_ne_zero_of_ne at hf
  specialize h (|x - y| / 2) ?_
  · simp
    exact hf
  · obtain ⟨N, h⟩ := h
    specialize h N le_rfl
    contrapose h
    simp [hf]

lemma k_inv (x : MyRat) : k x⁻¹ = (k x)⁻¹ := by
  simp [k, inv_def]
  intro ε εh
  by_cases h : x = 0
  · have := k_zero
    rw [← h, zero_def, k, Quotient.eq_iff_equiv] at this
    simp [h, MyPrereal.inv, ↓this]
    use 0
    intro n hn
    linarith
  · have : k x ≠ 0
    · rw [← k_zero]
      intro hf
      apply k_injective at hf
      contradiction
    rw [zero_def, k, ne_eq, Quotient.eq_iff_equiv] at this
    simp [MyPrereal.inv, this]
    use 0
    intro n hn
    linarith

@[simp] lemma k_inj {x y : MyRat} : k x = k y ↔ x = y :=
  k_injective.eq_iff

end MyReal

namespace MyPrereal

def IsPos (x : MyPrereal) : Prop :=
  ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ ≤ x n

open Filter

/-- Filter.eventually version of IsPos -/
lemma isPos_def' (x : MyPrereal) : IsPos x ↔ ∃ δ, 0 < δ ∧ ∀ᶠ n in atTop, δ ≤ x n := by
  simp only [eventually_atTop]
  rfl

lemma pos_of_isPos {x : MyPrereal} (hx : IsPos x) :
    ∃ N, ∀ n, N ≤ n → 0 < x n := by
  obtain ⟨δ, δh, N, hN⟩ := hx
  use N
  intro n hn
  specialize hN n hn
  linarith

#check Eventually.mono
#check Eventually.mp
#check EventuallyLE.trans

lemma eventually_lt_of_le_of_lt {a b c : ℕ → MyRat} (H₁ : ∀ᶠ (n : ℕ) in atTop, a n ≤ b n) (H₂ : ∀ᶠ (n : ℕ) in atTop, b n < c n) : ∀ᶠ (n : ℕ) in atTop, a n < c n :=
  H₂.mp <| H₁.mono fun _ => lt_of_le_of_lt

lemma eventually_lt_of_lt_of_le {a b c : ℕ → MyRat} (H₁ : ∀ᶠ (n : ℕ) in atTop, a n < b n) (H₂ : ∀ᶠ (n : ℕ) in atTop, b n ≤ c n) : ∀ᶠ (n : ℕ) in atTop, a n < c n :=
  H₂.mp <| H₁.mono fun _ => lt_of_lt_of_le

lemma pos_of_isPos' {x : MyPrereal} (hx : IsPos x) :
    ∀ᶠ n in atTop, 0 < x n := by
  rw [isPos_def'] at hx
  obtain ⟨δ, δh, hx⟩ := hx
  apply eventually_lt_of_lt_of_le (eventually_const.mpr δh) hx

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

-- Should be called IsNonneg_of_eventually_nonneg
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
@[simp] lemma not_eventually_atTop_false {α : Type*} [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] : ¬ ∀ᶠ (_ : α) in atTop, False := by
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

end MyPrereal

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

instance : PartialOrder MyReal where
  le := (. ≤ .)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

instance : ZeroLEOneClass MyReal := ⟨zero_le_one⟩

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

theorem MyPrereal.equiv_const {a b : MyRat} : a = b ↔ MyPrereal.R_equiv ⟨_, IsCauchy.const a⟩ ⟨_, IsCauchy.const b⟩ := by
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

noncomputable instance : IsStrictOrderedRing MyReal :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma myRat_dense_rat' (x : MyReal) {ε : MyRat} (hε : 0 < ε) : ∃ r, |x - k r| < k ε := by
  induction' x using Quotient.inductionOn with x
  -- Begin by getting a tight bound on the sequence
  have cauchy := x.2 (ε / 4) (by linarith)
  simp only [← coe_apply'] at cauchy
  obtain ⟨N, cauchy⟩ := cauchy
  use x N
  rw [abs_lt]
  constructor
  · suffices -⟦x⟧ < k (ε - x N) by
      rw [k_sub] at this
      linarith
    rw [lt_iff_le_and_ne]
    constructor
    · rw [k, le_def, neg_def, sub_def, isNonneg_def, MyPrereal.IsNonneg]
      left
      simp [IsPos]
      refine ⟨ε / 4, by linarith, N, ?_⟩
      intro n hn
      specialize cauchy N n le_rfl hn
      simp [abs_le] at cauchy
      linarith
    · intro hf
      simp [k, neg_def] at hf
      specialize hf (ε / 2) (by linarith)
      obtain ⟨M, hM⟩ := hf
      specialize hM (max M N) le_sup_left
      specialize cauchy (max M N) N le_sup_right le_rfl
      simp [abs_le] at *
      linarith
  · rw [sub_lt_iff_lt_add, ← k_add]
    rw [lt_iff_le_and_ne]
    constructor
    · rw [k, le_def, sub_def, isNonneg_def, MyPrereal.IsNonneg]
      left
      simp [IsPos]
      refine ⟨ε / 4, by linarith, N, ?_⟩
      intro n hn
      specialize cauchy N n le_rfl hn
      simp [abs_le] at cauchy
      linarith
    · intro hf
      simp [k] at hf
      specialize hf (ε / 2) (by linarith)
      obtain ⟨M, hM⟩ := hf
      specialize hM (max M N) le_sup_left
      specialize cauchy (max M N) N le_sup_right le_rfl
      simp [abs_le] at *
      linarith

open Filter

lemma myRat_dense_of_pos {x : MyReal} (hx : 0 < x) : ∃ r, 0 < r ∧ k r < x := by
  -- either x ≤ 1 or x⁻¹ < 1
  -- right case is trivial, use r = 1
  -- left case: x ≤ 1
  -- ⊢ 0 < k r < x ≤ 1
  -- ⊢ k r⁻¹ > x⁻¹ ≥ 1
  -- because x⁻¹ is cauchy, it is bounded by B (which is > 0)
  -- B ≥ "x⁻¹ n", now B⁻¹ ≤ "x n", for all n (by quotient induction)

  have : x = 1 ∨ x⁻¹ < 1 ∨ x < 1
  · rw [or_iff_not_imp_left]
    intro h
    rw [inv_lt_one_iff₀]
    rcases le_or_gt x 1 with h' | h'
    · have := lt_of_le_of_ne h' h
      tauto
    · tauto

  rcases this with rfl | h | h
  · -- x = 1
    use 1/2
    simp [k, one_def]
    rw [← sub_pos, sub_def, ← pos_def]
    refine ⟨1/2, by linarith, 0, ?_⟩
    norm_num

  · -- x⁻¹ < 1
    refine ⟨1, by linarith, ?_⟩
    rw [inv_lt_one_iff₀] at h
    rcases h with h | h
    · linarith
    induction' x using Quotient.inductionOn with x
    rw [← pos_def] at hx

    rw [one_def, ← sub_pos, sub_def, ← pos_def] at h
    rw [k, ← sub_pos, sub_def, ← pos_def]
    exact h

  · -- x < 1
    induction' x using Quotient.inductionOn with x
    rw [← sub_pos, one_def, sub_def] at h

    have hx0 : ¬ x ≈ 0
    · obtain ⟨hx0, hx1⟩ := lt_iff_le_and_ne.mp hx
      rw [← Quotient.eq_iff_equiv]
      exact hx1 ∘ symm

    rw [← pos_def] at h
    rw [← pos_def] at hx
    rw [isPos_def'] at *
    obtain ⟨δ, δh, h⟩ := h
    obtain ⟨ε, εh, hx⟩ := hx
    have h_and_hx := Eventually.and h hx

    -- Key lemma: eventually r < x n
    have : ∃ r > 0, ∀ᶠ n in atTop, r < x n
    · simp at h_and_hx
      obtain ⟨N, hN⟩ := h_and_hx
      obtain ⟨R, hR, hxinv⟩ := x.inv.2.bounded
      let r := (R * 2)⁻¹
      have hr : ∀ n ≥ N, r < |x n|
      · intro n hn
        specialize hxinv n
        rw [← inv_inv |x n|]

        rw [inv_lt_inv₀ (by linarith)]
        · rw [← abs_inv]
          rw [← MyPrereal.inv_def hx0]
          rw [coe_apply]
          linarith
        · rw [inv_pos, abs_pos]
          specialize hN n hn
          obtain ⟨-, hN2⟩ := hN
          linarith

      use r
      constructor
      · exact inv_pos.mpr (by linarith)
      · simp
        use N
        intro n hn
        specialize hr n hn
        suffices 0 ≤ x n by
          rw [abs_of_nonneg this] at hr
          exact hr
        specialize hN n hn
        linarith

    obtain ⟨r, hr, h⟩ := this
    refine ⟨r / 2, by linarith, ?_⟩

    suffices 0 < (⟦x - ⟨_, IsCauchy.const _⟩⟧ : MyReal) by
      rw [← sub_def, sub_pos] at this
      rw [k]
      linarith

    rw [← pos_def, IsPos]
    refine ⟨r / 2, by linarith, ?_⟩
    rw [← eventually_atTop]
    apply h.mono
    intro n hn
    simp
    linarith


-- TODO why is this named _rat?
lemma myRat_dense_rat (x : MyReal) {ε : MyReal} (hε : 0 < ε) : ∃ r, |x - k r| < ε := by
  obtain ⟨εr, hεr⟩ := myRat_dense_of_pos hε
  have := myRat_dense_rat' x hεr.1
  apply Exists.imp _ this
  intro r hr
  linarith

abbrev TendsTo (f : ℕ → MyReal) (x : MyReal) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |f n - x| ≤ ε

lemma tendsTo_of_myRat_tendsTo {f : ℕ → MyReal} {x : MyReal}
    (h : ∀ (ε : MyRat), 0 < ε → ∃ N, ∀ n, N ≤ n → |f n - x| ≤ k ε) : TendsTo f x := by
  intro ε εh
  -- apply myRat_dense_rat
  obtain ⟨εr, hεr⟩ := myRat_dense_of_pos εh
  specialize h εr hεr.1
  rw [← eventually_atTop] at *
  apply h.mono
  intro n nh
  linarith

abbrev IsConvergent (f : ℕ → MyReal) : Prop :=
  ∃ x, TendsTo f x

#check IsCauchy

-- Why shadow previous definition?
abbrev IsCauchy (f : ℕ → MyReal) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |f p - f q| ≤ ε

lemma tendsTo_myRat (x : MyPrereal) : TendsTo (fun n ↦ k (x n)) ⟦x⟧ := by
  apply tendsTo_of_myRat_tendsTo
  intro ε εh
  have cauchy := x.2 (ε/2) (by linarith)
  apply cauchy.imp
  intro N hN n hn

  rw [abs_le]
  simp [k, add_def, le_def, sub_def, IsNonneg]
  rw [MyPrereal.IsNonneg]
  constructor <;>
  · left
    refine ⟨ε/2, by linarith, N, ?_⟩
    intro n' hn'
    specialize hN n n' hn hn'
    simp
    simp [abs_le, ← coe_apply'] at hN
    linarith

section completeness

-- this looks really ugly with explicit coercions
lemma ex_approx_punctual (x : MyReal) (n : ℕ) :
    ∃ (r : MyRat), |x - k r| < k ((MyRat.i (n+1))⁻¹) := by
  apply myRat_dense_rat'
  -- TODO improve simp so that it can solve this
  rw [inv_pos]
  rw [MyRat.i_add]
  suffices 0 ≤ MyRat.i n by
    grw [← this]
    simp [MyRat.i, ← MyRat.one_def]
  rw [← MyRat.i_zero, MyRat.i_le_iff]
  exact Nat.zero_le n

lemma ex_approx (f : ℕ → MyReal) :
    ∃ (g : ℕ → MyRat), ∀ n, |f n - k (g n)| < k ((MyRat.i (n+1))⁻¹) := by
  -- skolemize ex_approx_punctual to get g
  have hg (n) := ex_approx_punctual (f n) n
  choose g h using hg
  exact ⟨g, h⟩

noncomputable def approx (f : ℕ → MyReal) : ℕ → MyRat := (ex_approx f).choose

lemma approx_spec (f : ℕ → MyReal) : ∀ n, |f n - k ((approx f) n)| < k ((MyRat.i (n+1))⁻¹) :=
  (ex_approx f).choose_spec

-- Why + 1?
-- lemma archimedean (x : MyReal) : ∃ (n : ℕ), x ≤ k (MyRat.i (n + 1)) := by
lemma archimedean (x : MyReal) : ∃ (n : ℕ), x ≤ k (MyRat.i n) := by
  rcases le_or_gt x 0 with h | h
  · use 0
    grw [h, ← k_zero]
    rw [k_le_iff]
    simp [MyRat.i_zero]
  ·
    -- choose a rational number > x
    obtain ⟨r, hr⟩ := myRat_dense_rat (2 * x) h
    -- induction' r using Quotient.inductionOn with r
    obtain ⟨n, hn⟩ := MyRat.archimedean r
    use n
    have : k r > x
    · rw [abs_lt] at hr
      linarith
    grw [← this]
    rw [k_le_iff]
    exact hn

lemma archimedean0 {x : MyReal} (hx : 0 < x) : ∃ (n : ℕ), k (MyRat.i (n + 1))⁻¹ ≤ x := by
  have := archimedean x⁻¹
  apply this.imp
  intro n h
  rw [← inv_inv x, k_inv, inv_le_inv₀]
  · grw [h]
    rw [k_le_iff, MyRat.i_le_iff]
    linarith
  · rw [← k_zero, k_lt_iff, ← MyRat.i_zero, MyRat.i_lt_iff]
    linarith
  · exact inv_pos.mpr hx

-- These would be marked push_cast I suppose
lemma k_div {a b : MyRat} : k (a / b) = (k a / k b) := by
  simp [div_eq_mul_inv, k_mul, k_inv]

lemma k_abs {a : MyRat} : k |a| = |k a| := by
  by_cases ha : a < 0
  · have : k a < 0
    · rw [← k_zero, k_lt_iff]
      exact ha
    simp [abs_of_neg, ha, this]
  · simp at ha
    have : 0 ≤ k a
    · rw [← k_zero, k_le_iff]
      exact ha
    simp [abs_of_nonneg, ha, this]

lemma approx_cauchy {f : ℕ → MyReal} (hf : IsCauchy f) : _root_.IsCauchy (approx f) := by
  intro ε εh
  have spec := approx_spec f
  --   |approx f p - approx f q|
  -- ≤ |approx f p - approx f q + f q - f p| + |f p - f q|
  -- = |(f q - approx f q) - (f p - approx f p)| + |f p - f q|
  -- ≤ |f q - approx f q| + |f p - approx f p| + |f p - f q|
  -- ≤ (p + q + 2)/(q + 1)(p + 1) + |f p - f q|
  -- ≤ 2/N + |f p - f q|
  -- whic needs to be ≤ ε
  -- => N ≥ 2/ε, let's use 4/ε to be sure

  obtain ⟨N, hN, hN2⟩ : ∃ N, 4 / ε ≤ MyRat.i N ∧ N > 0
  · obtain ⟨N, hN⟩ := MyRat.archimedean (4 / ε)
    refine ⟨N + 1, ?_, by linarith⟩
    grw [hN]
    rw [MyRat.i_le_iff]
    linarith

  specialize hf (k (1 / MyRat.i N)) ?_
  ·
    rw [← k_zero, k_lt_iff]
    apply div_pos
    linarith
    rw [← MyRat.i_zero, MyRat.i_lt_iff]
    linarith

  obtain ⟨M, hM⟩ := hf

  use max N M

  intro p q hp hq
  rw [sup_le_iff] at *
  specialize hM _ _ hp.2 hq.2

  have sp := spec p
  have sq := spec q
  have hp1 : (MyRat.i (p + 1))⁻¹ ≤ (MyRat.i N)⁻¹
  · rw [inv_le_inv₀]
    · rw [MyRat.i_le_iff]
      linarith
    · rw [← MyRat.i_zero, MyRat.i_lt_iff]
      linarith
    · rw [← MyRat.i_zero, MyRat.i_lt_iff]
      linarith

  have hq1 : (MyRat.i (q + 1))⁻¹ ≤ (MyRat.i N)⁻¹
  · rw [inv_le_inv₀]
    · rw [MyRat.i_le_iff]
      linarith
    · rw [← MyRat.i_zero, MyRat.i_lt_iff]
      linarith
    · rw [← MyRat.i_zero, MyRat.i_lt_iff]
      linarith

  rw [← k_le_iff] at hp1 hq1
  grw [hp1] at sp
  rw [abs_sub_comm] at sp
  grw [hq1] at sq

  -- Write ε in terms of N
  have : 4 / MyRat.i N ≤ ε
  · rw [div_le_comm₀]
    · exact hN
    · rw [← MyRat.i_zero, MyRat.i_lt_iff]
      linarith
    · exact εh
  grw [← this]

  rw [← k_le_iff, k_abs, k_sub]
  -- Use triangle inequality to get f q - f p inside |·|
  grw [abs_add' _ (f q - f p)]

  -- Reorder terms inside |·|
  rw [show
    |f q - f p + (k (approx f p) - k (approx f q))| =
    |f q - k (approx f q) + (k (approx f p) - f p)| by ring_nf]

  -- Use triangle inequality again to separate |· + ·|
  grw [abs_add]

  rw [abs_sub_comm]
  grw [sp, sq, hM]
  simp [← k_add, k_le_iff]
  ring_nf
  apply mul_le_mul le_rfl
  · norm_num
  · norm_num
  · rw [inv_nonneg, ← MyRat.i_zero, MyRat.i_le_iff]
    linarith

noncomputable
def IsCauchy.approx {f : ℕ → MyReal} (hf : IsCauchy f) : MyPrereal := ⟨_, approx_cauchy hf⟩

lemma IsCauchy.approx_def {f : ℕ → MyReal} (hf : IsCauchy f) : hf.approx = (⟨fun n => hf.approx n, approx_cauchy hf⟩ : MyPrereal) := by
  rfl

nonrec lemma IsCauchy.approx_spec {f : ℕ → MyReal} (hf : IsCauchy f) :
    ∀ n, |f n - k (hf.approx n)| < k ((MyRat.i (n+1))⁻¹) :=
  approx_spec f


lemma eventually_tendsto_mk'_rat {f : ℕ → MyReal} (hf : IsCauchy f) (ε : MyRat) (hε : 0 < ε) : ∀ᶠ n in atTop, |⟦hf.approx⟧ - k (hf.approx n)| ≤ k ε := by
  obtain ⟨M, hM⟩ := hf.approx.2 (ε / 2) (by linarith)
  rw [eventually_atTop]
  use M
  intro p hp

  by_cases h : ⟦hf.approx⟧ - k (hf.approx p) < 0
  · rw [abs_of_neg h]
    left
    simp [IsPos]
    refine ⟨ε / 2, by linarith, ?_⟩
    use M
    intro q hq
    specialize hM _ _ hp hq
    simp [abs_le, ← coe_apply'] at hM
    linarith
  · rw [not_lt] at h
    rw [abs_of_nonneg h]
    left
    simp [IsPos]
    refine ⟨ε / 2, by linarith, ?_⟩
    use M
    intro q hq
    specialize hM _ _ hp hq
    simp [abs_le, ← coe_apply'] at hM
    linarith

theorem complete {f : ℕ → MyReal} (hf : IsCauchy f) : IsConvergent f := by
  use ⟦hf.approx⟧

  apply tendsTo_of_myRat_tendsTo
  intro ε εh

  obtain ⟨N, hN, hN2⟩ : ∃ N, 2 / ε ≤ MyRat.i N ∧ N > 0
  · obtain ⟨N, hN⟩ := MyRat.archimedean (2 / ε)
    refine ⟨N + 1, ?_, by linarith⟩
    grw [hN]
    rw [MyRat.i_le_iff]
    linarith

  have h := eventually_tendsto_mk'_rat hf
  simp_rw [eventually_atTop] at h

  specialize h (1 / MyRat.i N) ?_
  ·
    apply div_pos
    linarith
    rw [← MyRat.i_zero, MyRat.i_lt_iff]
    linarith

  obtain ⟨M, hM⟩ := h

  use max N M
  intro n hn
  rw [sup_le_iff] at hn

  have hf_spec := hf.approx_spec n
  specialize hM _ hn.2
  have h2 : (MyRat.i (n + 1))⁻¹ ≤ ε/2
  · have : MyRat.i N ≤ MyRat.i (n + 1)
    · rw [MyRat.i_le_iff]
      linarith
    grw [← this]
    · grw [← hN]
      simp
    · rw [← MyRat.i_zero, MyRat.i_lt_iff]
      exact hN2

  have h3 : 1 / MyRat.i N ≤ ε/2
  · grw [← hN]
    simp
  rw [← k_le_iff] at h2 h3

  grw [h2] at hf_spec
  grw [h3] at hM
  rw [abs_sub_comm] at hM
  have : |f n - k (hf.approx n)| + |k (hf.approx n) - ⟦hf.approx⟧| ≤ 2 * k (ε / 2)
  · linarith

  grw [← abs_add] at this
  rw [two_mul, ← k_add] at this
  ring_nf at this
  exact this

end completeness

end MyReal
