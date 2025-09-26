import Mathlib
import Numbers.RealsComplete

#check ConditionallyCompleteLinearOrderedField
#check instConditionallyCompleteLinearOrderedFieldReal
#check ConditionallyCompleteLinearOrderedField

noncomputable section
namespace MyReal

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
