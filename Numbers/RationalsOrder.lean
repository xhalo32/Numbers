import Numbers.Rationals

/-!

# The order on the rationals

We prove that the rationals are a total order, and also that the ordering
plays well with the ring structure.

-/

namespace MyRat

/-

## Nonnegativitiy on the rationals

-/
-- this definition is somehow bad as it asks for proofs of b≠0 and b>0
def IsNonneg (x : MyRat) : Prop :=
  ∃ (a b : MyInt) (_ : 0 ≤ a) (hb : 0 < b), x = ⟦(a, ⟨b, hb.ne'⟩)⟧

/-

### Relationship with 0 and 1

-/

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  unfold IsNonneg
  rw [zero_def]
  use 0
  use 1
  have h1 : (0 : MyInt) ≤ 0 := by rfl
  use h1
  have h2 : (0 : MyInt) < 1 := by linarith
  use h2

@[simp]
lemma one_nonneg : IsNonneg 1 := by
  unfold IsNonneg
  rw [one_def]
  have h1 : (0 : MyInt) < 1 := by linarith
  have h2 : (0 : MyInt) ≤ 1 := by linarith
  refine ⟨1, 1, h2, h1, rfl⟩

/-

## Relationship with neg

-/

lemma nonneg_neg {x : MyRat} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x = 0 := by
  unfold IsNonneg at *
  obtain ⟨a, b, h1, h2, h⟩ := h
  obtain ⟨a', b', h1', h2', h'⟩ := h'
  rw [zero_def]
  induction' x using Quotient.inductionOn with x
  simp_all
  have : x.2.val < 0 ∨ x.2.val > 0
  · simp [x.2.prop]

  rcases this with hx | hx
  · apply le_antisymm
    · rw [← mul_le_mul_right_of_neg $ show -b < 0 by linarith, zero_mul, mul_neg]
      grw [h, hx]
      simp
    · rw [← mul_le_mul_right_of_neg $ show -b' < 0 by linarith, zero_mul, mul_neg]
      grw [h', hx]
      simp
  · apply le_antisymm
    · rw [← mul_le_mul_right_of_neg $ show -b' < 0 by linarith, zero_mul, mul_neg]
      grw [h', hx]
      simp
    · rw [← mul_le_mul_right_of_neg $ show -b < 0 by linarith, zero_mul, mul_neg]
      grw [h, hx]
      simp


-- this one is also useful
lemma nonneg_neg_of_not_nonneg {x : MyRat} : ¬ IsNonneg x → IsNonneg (-x) := by
  induction' x using Quotient.inductionOn with x
  intro h
  unfold IsNonneg at *
  push_neg at h
  simp at *

  by_cases hx : x.1 = 0
  · simp only [hx, zero_mul, neg_zero, zero_eq_mul]
    use 0
    simp [exists_zero_lt]
  ·
    -- split into four cases
    have hx2 : x.2.val < 0 ∨ x.2.val > 0
    · simp [x.2.prop]
    have hx1 : x.1 < 0 ∨ x.1 > 0
    · simp [hx]

    rcases hx1 with hx1 | hx1
    · rcases hx2 with hx2 | hx2
      · specialize h (-x.1) (-x.2) (neg_nonneg_of_nonpos hx1.le) (Left.neg_pos_iff.mpr hx2)
        rw [mul_neg, mul_neg, neg_inj, mul_comm] at h
        contradiction
      · refine ⟨-x.1, x.2, hx2, neg_nonneg_of_nonpos hx1.le, ?_⟩
        ring

    · rcases hx2 with hx2 | hx2
      · refine ⟨x.1, -x.2, Left.neg_pos_iff.mpr hx2, hx1.le, ?_⟩
        ring
      · specialize h x.1 x.2 hx1.le hx2
        rw [mul_comm] at h
        contradiction

/-

## Relationship with addition

-/

lemma isNonneg_add_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x + y) := by
  unfold IsNonneg at *
  simp at *
  obtain ⟨a, ha, b, hb, hx⟩ := hx
  obtain ⟨c, hc, d, hd, hy⟩ := hy
  simp [hx, hy, add_def]

  refine ⟨a * d + b * c, ?_, b * d, ?_⟩
  · apply add_nonneg
    · exact (mul_nonneg_iff_of_pos_right hd).mpr ha
    · exact (mul_nonneg_iff_of_pos_left hb).mpr hc
  · simp_all
    ring

  -- This is what happens if you try to use quotient induction
  -- induction' x using Quotient.inductionOn with x
  -- induction' y using Quotient.inductionOn with y
  -- use ?_
  -- refine ⟨b * y.2 + d * x.2, ?_, ?_, ?_⟩
  -- · sorry
  -- · sorry
  -- · simp [add_mul, mul_add]
  --   calc _ = x.1 * b * y.2^2 + x.2 * y.1 * b * y.2 + (x.1 * y.2 * d * x.2 + x.2^2 * y.1 * d) := by ring
  --        _ = x.2 * a * y.2^2 + x.2 * y.1 * b * y.2 + (x.1 * y.2 * d * x.2 + x.2^2 * y.1 * d) := by rw [hab]
  --        _ = x.2 * a * y.2^2 + x.2 * y.1 * b * y.2 + (x.1 * y.2 * d * x.2 + x.2^2 * (y.1 * d)) := by ac_rfl
  --        _ = x.2 * a * y.2^2 + x.2 * y.1 * b * y.2 + (x.1 * y.2 * d * x.2 + x.2^2 * y.2 * c) := by rw [hcd]; ring

  --   calc _ = x.2 * y.2 * (a * y.2 + y.1 * b)       + y.2 * x.2 * (x.1 * d + x.2 * c) := by simp [mul_add]; ring
  --       --  _ = x.2 * y.2 * ?w := by sorry


/-

## Relationship with multiplication

-/

-- github copilot wrote the first proof I had of this
lemma isNonneg_mul_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x * y) := by
  unfold IsNonneg at *
  simp at *
  obtain ⟨a, ha, b, hb, hx⟩ := hx
  obtain ⟨c, hc, d, hd, hy⟩ := hy
  simp [hx, hy, mul_def]

  refine ⟨a * c, ?_, b * d, ?_⟩
  · exact Left.mul_nonneg ha hc
  · simp_all
    ring

/-

## Relationship with inverse

-/

lemma isNonneg_inv_isNonneg {x : MyRat} (hx : IsNonneg x) :
    IsNonneg x⁻¹ := by
  unfold IsNonneg at *
  simp at *
  obtain ⟨a, ha, b, hb, hx⟩ := hx
  by_cases ha : a = 0
  · simp [hx, inv_def, MyPrerat.inv_def', ha]
    exact exists_zero_lt
  · simp [hx, inv_def, MyPrerat.inv_def _ ha]
    refine ⟨b, hb.le, a, ?_, mul_comm _ _⟩
    apply lt_of_le_of_ne (by assumption) (ha ∘ symm)

/-!

## The linear order on the rationals

I think that's it for non-negativity on the rationals. Let's see
if we can use those theorems about nonnegativity to prove that
the raionals are a linear order.

-/

/-- Our definition of x ≤ y on the rationals. -/
def le (x y : MyRat) : Prop := IsNonneg (y - x)

instance : LE MyRat where
  le := le

lemma le_def (x y : MyRat) : x ≤ y ↔ IsNonneg (y - x) := by
  rfl

-- The following doesn't hold because a.2 and b.2 can be negative
-- lemma le_def' (a b : MyPrerat) : (⟦a⟧ : MyRat) ≤ ⟦b⟧ ↔ a.1 * b.2 ≤ a.2 * b.1 := by
--   -- rw [← sub_nonneg]
--   cases' a with a1 a2
--   cases' b with b1 b2
--   simp
--   constructor
--   · intro h
--     simp [le_def, sub_eq_add_neg, add_def] at h

--     -- This should be a lemma
--     have : b2.val * a2 < 0 ∨ b2.val * a2 > 0
--     · by_cases h2 : b2.val * a2 < 0
--       · tauto
--       · right
--         simp at h2
--         rw [mul_nonneg_iff] at h2
--         rcases h2 with h2 | h2
--         · apply mul_pos
--           · exact lt_of_le_of_ne' h2.1 b2.prop
--           · exact lt_of_le_of_ne' h2.2 a2.prop
--         · apply mul_pos_of_neg_of_neg
--           · exact lt_of_le_of_ne h2.1 b2.prop
--           · exact lt_of_le_of_ne h2.2 a2.prop

--     obtain ⟨c, d, hc,hd, h⟩ := h
--     simp at h
--     suffices b2 * a1 - b1 * a2 ≤ 0 by linarith


--     rcases this with h2 | h2
--     · rw [lt_iff_le_and_ne] at h2
--       obtain ⟨h21, h22⟩ := h2
--       have := mul_nonpos_of_nonpos_of_nonneg h21 hc
--       rw [← h] at this
--       -- rw [mul_nonpos_iff_pos_imp_nonpos]
--       rw [mul_nonpos_iff] at this
--       rcases this with h | h
--       · linarith
--       · simp at h ⊢

lemma zero_le_iff_IsNonneg (x : MyRat) : 0 ≤ x ↔ IsNonneg x := by
  induction' x using Quotient.inductionOn with x
  rw [zero_def, le_def, sub_eq_add_neg, neg_def, add_def]
  simp [MyInt.ne_zero_mk_one_eq_one]

/-!

We now develop some basic theory of `≤` on the rationals.
Let's warm up with 0 ≤ 1.

-/

lemma zero_le_one : (0 : MyRat) ≤ 1 := by
  simp [le_def]

/-!

There's no point proving 0 ≤ 0 and 1 ≤ 1, we may as well prove reflexivity
in general.

-/

lemma le_refl (x : MyRat) : x ≤ x := by
  simp [le_def]

/-!

Next is transitivitiy

-/

lemma le_trans (x y z : MyRat) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  simp [le_def] at *
  rw [show z - x = y - x + (z - y) by ring]
  apply isNonneg_add_isNonneg h1 h2

/-!

Next is antisymmetry

-/

lemma le_antisymm (x y : MyRat) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  simp [le_def] at *
  suffices x - y = 0 by
    rw [sub_eq_zero] at this
    exact this
  apply nonneg_neg hyx
  simp
  exact hxy

instance : PartialOrder MyRat where
  le := (. ≤ .)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

instance : ZeroLEOneClass MyRat := ⟨zero_le_one⟩

lemma isNonneg_iff (x : MyRat) : IsNonneg x ↔ 0 ≤ x := by
  simp [le_def]

lemma add_le_add_left (x y : MyRat) (h : x ≤ y) (t : MyRat) : t + x ≤ t + y := by
  simp_all [le_def]

lemma mul_nonneg (x y : MyRat) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  induction' x using Quotient.inductionOn with x
  induction' y using Quotient.inductionOn with y
  rw [← isNonneg_iff] at *
  obtain ⟨a, b, ha, hb, hx⟩ := hx
  obtain ⟨c, d, hc, hd, hy⟩ := hy
  simp_all


  have hx2 : x.2.val < 0 ∨ x.2.val > 0
  · simp [x.2.prop]
  have hy2 : y.2.val < 0 ∨ y.2.val > 0
  · simp [y.2.prop]

  rcases hx2 with hx2 | hx2
  ·
    rcases hy2 with hy2 | hy2
    · refine ⟨x.1 * y.1, x.2 * y.2, ?_, ?_, ?_⟩
      · rw [← neg_mul_neg]
        apply Left.mul_nonneg
        · rw [← mul_nonneg_iff_of_pos_right hb, neg_mul, hx]
          grw [hx2]
          simp
        · rw [← mul_nonneg_iff_of_pos_right hd, neg_mul, hy]
          grw [hy2]
          simp
      · exact mul_pos_of_neg_of_neg hx2 hy2
      · simp [mul_def']
        ring

    · refine ⟨-x.1 * y.1, -x.2 * y.2, ?_, ?_, ?_⟩
      ·
        apply Left.mul_nonneg
        · rw [← mul_nonneg_iff_of_pos_right hb, neg_mul, hx]
          grw [hx2]
          simp
        · rw [← mul_nonneg_iff_of_pos_right hd, hy]
          grw [hy2]
          simp
      · apply mul_pos _ hy2
        exact Left.neg_pos_iff.mpr hx2

      · simp [mul_def']
        ring
  ·
    rcases hy2 with hy2 | hy2
    · refine ⟨x.1 * -y.1, x.2 * -y.2, ?_, ?_, ?_⟩
      ·
        apply Left.mul_nonneg
        · rw [← mul_nonneg_iff_of_pos_right hb, hx]
          grw [hx2]
          simp
        · rw [← mul_nonneg_iff_of_pos_right hd, neg_mul, hy]
          grw [hy2]
          simp
      · apply mul_pos hx2
        exact Left.neg_pos_iff.mpr hy2

      · simp [mul_def']
        ring

    · refine ⟨-x.1 * -y.1, -x.2 * -y.2, ?_, ?_, ?_⟩
      · rw [neg_mul_neg]
        apply Left.mul_nonneg
        · rw [← mul_nonneg_iff_of_pos_right hb, hx]
          grw [hx2]
          simp
        · rw [← mul_nonneg_iff_of_pos_right hd, hy]
          grw [hy2]
          simp
      · rw [neg_mul_neg]
        exact mul_pos hx2 hy2
      · simp [mul_def']
        ring


instance : IsOrderedAddMonoid MyRat where
  add_le_add_left := add_le_add_left

instance : IsOrderedRing MyRat :=
  IsOrderedRing.of_mul_nonneg mul_nonneg

/-!

The interplay between the ordering and the natural maps from
the naturals and integers to the rationals.

-/

-- let's do `j` first, then we can use it for `i`

#check Int.le_of_sub_nonpos

/-- The natural map from the integers to the rationals
preserves and reflects `≤`.

- Preservation is the same as monotonicity: `p ≤ q` implies `j p ≤ j q`
- Reflection is like injectivity, but for ≤: `j p ≤ j q` implies `p ≤ q`
-/
lemma j_le_iff (p q : MyInt) : j p ≤ j q ↔ p ≤ q := by
  rw [← sub_nonpos, ← sub_nonpos (a := p)]
  convert_to j (p - q) ≤ 0 ↔ p - q ≤ 0
  rw [sub_eq_add_neg, sub_eq_add_neg, j_add, j_neg]

  simp [j, zero_def, le_def]
  rw [sub_eq_add_neg, neg_def, add_def, zero_mul, zero_add, one_mul, neg_sub, MyInt.ne_zero_mk_one_eq_one, one_mul]

  constructor
  · intro h
    obtain ⟨a, b, ha, hb, h⟩ := h
    simp at h
    suffices 0 ≤ q - p by
      linarith
    obtain ⟨h1, h2⟩ := le_antisymm_iff.mp h
    rw [← mul_le_mul_iff_of_pos_right hb, zero_mul]
    linarith
  · intro h
    refine ⟨q - p, 1, sub_nonneg_of_le h, zero_lt_one, ?_⟩
    simp

-- lemma lt_def (a b : MyPrerat) : (⟦a⟧ : MyRat) < ⟦b⟧ ↔ a.1 * b.2 < a.2 * b.1 := by
--   rw [← sub_pos]
--   simp [lt_iff_le_and_ne]
--   cases' a with a1 a2
--   cases' b with b1 b2
--   constructor
--   · intro h
--     simp [le_def, sub_eq_add_neg, add_def] at h
--     simp [zero_def] at h
--     simp [lt_iff_le_and_ne]
--     constructor
--     ·

lemma j_lt_iff (p q : MyInt) : j p < j q ↔ p < q := by
  simp [lt_iff_le_and_ne]
  have := j_le_iff p q
  rw [this]
  apply and_congr_right
  intro h
  apply not_congr
  exact j_injective p q

/-!

## Linear order structure on the rationals

-/

def le_total (a b : MyRat) : a ≤ b ∨ b ≤ a := by
  by_cases h : a ≤ b
  · simp_all
  · right
    simp [le_def] at h
    apply nonneg_neg_of_not_nonneg at h
    simp at h
    exact h

noncomputable instance linearOrder : LinearOrder MyRat where
  le_total := le_total
  toDecidableLE := Classical.decRel _

lemma mul_pos (a b : MyRat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [lt_iff_le_and_ne] at *
  have := mul_nonneg a b
  simp_all
  tauto

noncomputable instance : IsStrictOrderedRing MyRat :=
  IsStrictOrderedRing.of_mul_pos mul_pos

/-- The natural map from the naturals to the rationals preserves
and reflects `≤`. -/
lemma i_le_iff (a b : ℕ) : i a ≤ i b ↔ a ≤ b := by
  simp

lemma i_lt_iff (a b : ℕ) : i a < i b ↔ a < b := by
  simp

lemma archimedean (x : MyRat) : ∃ (n : ℕ), x ≤ i n := by
  induction' x using Quotient.inductionOn with x
  cases' x with x1 x2
  by_cases hx : x1 ≥ 0
  · obtain ⟨n, hn⟩ := hx
    simp at hn
    cases hn
    use n
    simp [i]
    rw [le_def, sub_eq_add_neg, neg_def, add_def]
    simp [MyInt.ne_zero_mk_one_eq_one]

    have hx2 : x2.val < 0 ∨ x2.val > 0
    · simp [x2.prop]
    rcases hx2 with hx2 | hx2
    · refine ⟨-(n * x2 - n), -x2, ?_, ?_, ?_⟩
      · simp
        apply le_trans' (Nat.cast_nonneg' n)
        exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg' n) hx2.le
      · exact Left.neg_pos_iff.mpr hx2
      · simp
        ring
    · refine ⟨n * x2 - n, x2, ?_, ?_, ?_⟩
      · simp
        apply le_mul_of_one_le_right (Nat.cast_nonneg' n)
        apply MyInt.one_le_of_zero_lt
        exact hx2
      · exact hx2
      · simp
        ring
  · simp at hx
    rw [lt_iff_le_and_ne] at hx
    obtain ⟨n, hn⟩ := hx.1
    simp at hn
    use n
    simp [i]
    rw [le_def, sub_eq_add_neg, neg_def, add_def]
    simp [MyInt.ne_zero_mk_one_eq_one]

    have x1h : -x1 = n
    · linarith

    have hx2 : x2.val < 0 ∨ x2.val > 0
    · simp [x2.prop]
    rcases hx2 with hx2 | hx2
    · refine ⟨-(n * x2 + n), -x2, ?_, ?_, ?_⟩
      · rw [le_neg, neg_zero]
        suffices n * (x2.val + 1) ≤ 0 by
          linarith
        apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg' n)
        have := MyInt.one_le_of_zero_lt (-x2) (by linarith)
        linarith
      · exact Left.neg_pos_iff.mpr hx2
      · simp
        rw [x1h]
        ring
    · refine ⟨n * x2 + n, x2, ?_, ?_, ?_⟩
      · grw [hx2]
        simp
      · exact hx2
      · simp
        rw [x1h]
        ring

instance : Archimedean MyRat := by
  rw [archimedean_iff_nat_le]
  simp_rw [natCast_eq]
  intro x
  exact archimedean x

end MyRat

/-

Both of these now work

#synth LinearOrder MyRat
#synth IsStrictOrderedRing MyRat

-/
