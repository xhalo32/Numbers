import Numbers.RationalsOrder

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

-- This is never used
-- lemma prop (x : MyPrereal) : ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε :=
  -- x.2

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

-- In rationals.lean, we did not define Zero for pre-rationals...
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

instance neg : Neg MyPrereal where
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

instance add : Add MyPrereal where
  add x y := ⟨x + y, x.2.add y.2⟩

instance sub : Sub MyPrereal where
  sub x y := x + -y

@[simp] lemma add_def (x y : MyPrereal) (n : ℕ) : (x + y) n = x n + y n := by
  rfl

@[simp] lemma add_def' (x y : MyPrereal) (n : ℕ) : (x + y).val n = x n + y n := by
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

instance mul : Mul MyPrereal where
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

@[simp] lemma sub_def (x y : MyPrereal) (n : ℕ) : (x - y) n = x n - y n := by
  rfl

@[simp] lemma sub_def' (x y : MyPrereal) (n : ℕ) : (x - y).val n = x n - y n := by
  rfl

lemma IsCauchy.sub {f g : ℕ → MyRat} (hf : IsCauchy f) (hg : IsCauchy g) : IsCauchy (f - g) := by
  rw [sub_eq_add_neg]
  apply add hf
  exact neg hg

@[simp] lemma sub_def'' {f g : ℕ → MyRat} (hf : IsCauchy f) (hg : IsCauchy g) : (⟨fun n => f n, hf⟩ : MyPrereal) - ⟨fun n => g n, hg⟩ = ⟨fun n => f n - g n, IsCauchy.sub hf hg⟩ := by
  rfl

end MyPrereal

open MyPrereal

-- I would like this to be a def to avoid bad instances
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

macro "quot_proof" : tactic =>
  `(tactic|
  focus
    refine Quot.ind fun a => ?_
    try refine Quot.ind fun b => ?_
    try refine Quot.ind fun c => ?_
    apply Quot.sound
    intro ε hε
    simp
    use 0
    intro n hn
    try {ring_nf; simp [hε.le]}
  )

instance commRing : CommRing MyReal where
  add := (· + ·)
  add_assoc := by quot_proof
    -- refine Quot.ind fun a => ?_
    -- try refine Quot.ind fun b => ?_
    -- try refine Quot.ind fun c => ?_
    -- apply Quot.sound
    -- intro ε hε
    -- simp
    -- use 0
    -- intro n hn
    -- try {ring_nf; simp [hε.le]}
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

section injections

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

end injections

end MyReal
