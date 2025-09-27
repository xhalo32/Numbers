import Mathlib
import Numbers.RealsComplete

#check ConditionallyCompleteLinearOrderedField
#check instConditionallyCompleteLinearOrderedFieldReal
#check ConditionallyCompleteLinearOrderedField

noncomputable section
namespace MyReal

def ball (x : MyReal) {r : MyReal} (hr : r > 0) := { y | |x - y| < r }

instance : TopologicalSpace MyReal where
  IsOpen s := ∀ x ∈ s, ∃ r, ∃ (hr : r > 0), ball x hr ⊆ s
  isOpen_univ := by
    intro x _
    refine ⟨1, ?_, ?_⟩
    · simp
    · simp
  isOpen_inter := by
    intro s t hs ht
    simp [ball] at *
    intro x xs xt
    specialize hs _ xs
    specialize ht _ xt
    obtain ⟨rs, hrs, hs⟩ := hs
    obtain ⟨rt, hrt, ht⟩ := ht
    refine ⟨min rs rt, ?_, ?_, ?_⟩
    · intro y yh
      simp at yh
      exact hs yh.1
    · rw [lt_min_iff]
      exact ⟨hrs, hrt⟩
    · intro y yh
      simp at yh
      exact ht yh.2
  isOpen_sUnion := by
    sorry

-- instance : UniformSpace MyReal := sorry

-- #synth TopologicalSpace Real
-- instance : CompleteSpace MyReal := sorry

-- #check EMetric.complete_of_cauchySeq_tendsto

open MyRat in
theorem exists_isLUB {s : Set MyReal} (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x, IsLUB s x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : ∀ d : ℕ, BddAbove { m : MyInt | ∃ y ∈ s, MyReal.k (j m) ≤ y * d } := by
    obtain ⟨k, hk⟩ := exists_int_gt U
    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    rw [natCast_eq] at *
    rw [← j_le_iff, ← k_le_iff]
    apply le_trans' _ hy
    have := mul_le_mul_of_nonneg_right ((hU yS).trans hk.le) d.cast_nonneg
    rw [natCast_eq, intCast_eq, ← k_mul] at this
    simp [j_mul]
    simp at this
    exact this

  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ s, m ≤ y * d } := by
    intro d
    specialize this d
    simp_rw [intCast_eq]
    rcases this with ⟨U, hU⟩
    -- need to convert MyInt to ℤ
    sorry

  choose f hf using fun d : ℕ =>
    Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩

  have hf₁ : ∀ n > 0, ∃ y ∈ s, k (j (f n) / i n) ≤ y
  · intro n n0
    obtain ⟨y, yS, hy⟩ := (hf n).1
    rw [natCast_eq, intCast_eq] at hy
    refine ⟨y, yS, ?_⟩
    rw [k_div]
    rw [div_le_iff₀]
    · exact hy
    · rw [← k_zero, k_lt_iff, ← i_zero, i_lt_iff]
      exact n0

  have hf₂ : ∀ n : ℕ, n > 0 → ∀ y ∈ s, (y - (k (i n))⁻¹) < k (j (f n) / i n) := by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp only [gt_iff_lt]
    have k_pos : 0 < k (i n)
    · rwa [← k_zero, ← i_zero, k_lt_iff, i_lt_iff]
    rw [k_div, lt_div_iff₀]
    · rw [sub_mul, inv_mul_cancel₀ k_pos.ne']
      · rw [natCast_eq, intCast_eq] at this
        exact this
    · exact k_pos

  have hg : IsCauchy (fun n => k $ j (f n) / i n) := by
    intro ε εh
    suffices ∀ j ≥ ⌈ε⁻¹⌉₊, ∀ k ≥ ⌈ε⁻¹⌉₊, |(MyReal.k (MyRat.j (f j) / MyRat.i j) - MyReal.k (MyRat.j (f k) / MyRat.i k))| ≤ ε by
      constructor
      intro p q hp hq
      exact this p hp q hq
    intro j ij k ik
    sorry

  obtain ⟨x, hx_lim⟩ := complete hg
  refine ⟨x, ⟨fun x xS => ?_, fun y h => ?_⟩⟩
  · refine le_of_forall_lt_imp_le_of_dense fun z xz => ?_
    obtain ⟨K, hK⟩ := exists_nat_gt (x - z)⁻¹
    -- refine le_mk_of_forall_le ⟨K, fun n nK => ?_⟩
    -- replace xz := sub_pos.2 xz
    -- replace hK := hK.le.trans (Nat.cast_le.2 nK)
    -- have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    -- refine le_trans ?_ (hf₂ _ n0 _ xS).le
    -- rwa [le_sub_comm, inv_le_comm₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
    sorry
  sorry

-- This is the approach from Mathlib
open scoped Classical in
noncomputable instance : SupSet MyReal :=
  ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

open scoped Classical in
theorem sSup_def (s : Set MyReal) :
    sSup s = if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0 :=
  rfl

noncomputable instance : InfSet MyReal :=
  ⟨fun s => -sSup (-s)⟩

theorem sInf_def (s : Set MyReal) : sInf s = -sSup (-s) := rfl

protected theorem isLUB_sSup {s : Set MyReal} (h₁ : s.Nonempty) (h₂ : BddAbove s) : IsLUB s (sSup s) := by
  simp only [sSup_def, dif_pos (And.intro h₁ h₂)]
  apply Classical.choose_spec

protected theorem isGLB_sInf {s : Set MyReal} (h₁ : s.Nonempty) (h₂ : BddBelow s) : IsGLB s (sInf s) := by
  rw [sInf_def, ← isLUB_neg', neg_neg]
  exact MyReal.isLUB_sSup h₁.neg h₂.neg

noncomputable
instance lattice : Lattice MyReal :=
  inferInstance

noncomputable
instance : SemilatticeInf MyReal :=
  inferInstance

noncomputable
instance : SemilatticeSup MyReal :=
  inferInstance

noncomputable instance : ConditionallyCompleteLinearOrder MyReal where
  __ := MyReal.linearOrder
  __ := MyReal.lattice
  le_csSup s a hs ha := (MyReal.isLUB_sSup ⟨a, ha⟩ hs).1 ha
  csSup_le s a hs ha := (MyReal.isLUB_sSup hs ⟨a, ha⟩).2 ha
  csInf_le s a hs ha := (MyReal.isGLB_sInf ⟨a, ha⟩ hs).1 ha
  le_csInf s a hs ha := (MyReal.isGLB_sInf hs ⟨a, ha⟩).2 ha
  csSup_of_not_bddAbove s hs := by simp [hs, sSup_def]
  csInf_of_not_bddBelow s hs := by simp [hs, sInf_def, sSup_def]




-- We have ConditionallyCompleteLinearOrder and Field, which can now be combined
instance : ConditionallyCompleteLinearOrderedField MyReal := { }

#synth LinearOrder ℝ

-- To show that our Reals are isomorphic with Mathlib's, we need to construct the following
#check MyReal ≃+*o ℝ

-- This gives the induced isomorphism between conditionally complete linear ordered fields
#check LinearOrderedField.inducedOrderRingIso

abbrev inducedOrderRingIsoReal : MyReal ≃+*o ℝ := LinearOrderedField.inducedOrderRingIso MyReal ℝ

-- abbrev inducedEquiv : MyReal ≃ ℝ := inducedOrderRingIsoReal
-- abbrev inducedAddEquiv : MyReal ≃+ ℝ := inducedOrderRingIsoReal

-- This gives uniqueness up to isomorphism
#check LinearOrderedField.uniqueOrderRingIso

-- MyReals can automatically be coerced to Mathlib's ℝ
instance : Coe MyReal ℝ where
  coe := inducedOrderRingIsoReal

-- We can induce a matric space from Reals to MyReals using the isomorphism
-- This can be copied from Real.pseudoMetricSpace
instance : PseudoMetricSpace MyReal where
  dist x y := |x - y|
  dist_self := by simp
  dist_comm _ _ := abs_sub_comm _ _
  dist_triangle _ _ _ := abs_sub_le _ _ _

#synth PseudoMetricSpace MyReal

#synth TopologicalSpace MyReal -- this is wrong, need to override
instance (priority := 1000) : TopologicalSpace MyReal := PseudoMetricSpace.toUniformSpace.toTopologicalSpace

end MyReal

section Example

open MyReal

-- Now for some basic real analysis

def f (x : MyReal) : MyReal := x - 1

open Filter Topology in
example : Tendsto f (𝓝 3) (𝓝 2) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε εh
  use ε / 2 -- we are working with ℝ
  constructor
  · linarith
  · intro x hx
    unfold f
    simp [dist] at *
    rw [abs_lt] at *
    -- simp [LinearOrderedField.inducedMap]
    sorry

end Example

-- #min_imports
