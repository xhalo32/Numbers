import Mathlib.Tactic

#check Relation.EqvGen

-- As `complete` is `sound` in reveres, we get `r a b` ↔ `⟦a⟧ = ⟦b⟧`, which means `r` must be like `=`, i.e. an equivalence relation.
theorem Quot.complete {α : Sort*} {r : α → α → Prop} {a b : α} (hr : Equivalence r) (h : Quot.mk r a = Quot.mk r b) : r a b := by
  generalize mk r a = q at *
  -- refine q.rec ?_ ?_
  -- have := congrArg (lift id ?_) h

open Relation

/-
With Miika we attempted to show `Quot r ≃ Quot r.EqvGen`.
We clearly have a surjection `π` from left to right
Suffices to show injectivity:

  `∀ p q : Quot r, π p = π q → p = q`

Proof follows by quotient induction in `p` and `q`:

  `∀ a b : α, π ⟦a⟧ = π ⟦b⟧ → ⟦a⟧ = ⟦b⟧`

By completeness, `π ⟦a⟧ = π ⟦b⟧` gives us `r.EqvGen a b`.
To show `⟦a⟧ = ⟦b⟧` we write it as a sequence of symmetry and transitivity steps:
`⟦a⟧ = ⟦a'⟧ = ⟦b'⟧ = ⟦b⟧`, where we get `⟦a⟧ = ⟦a'⟧` from `r a a'`, `⟦a'⟧ = ⟦b'⟧` from `r b' a'` by symmetry of `=`, etc.
This process reduces `⟦a⟧ = ⟦b⟧` to `r a a' ∧ r b' a' ∧ r b' b` where all conjuncts are provable from induction on `r.EqvGen a b`.
-/

#check EqvGen.mono

noncomputable def Quot.equiv_eqvGen {α : Type*} {r : α → α → Prop} : Quot r ≃ Quot (EqvGen r) := by
  apply Equiv.ofBijective fun q => mk _ q.out
  constructor
  · intro p q h
    -- rw [Function.Injective]
    refine Quot.induction_on₂ p q ?_
    intro a b
    simp at h
    have := EqvGen.is_equivalence r
    apply complete this at h
    -- induction h
    -- apply TransGen.trans_induction_on
