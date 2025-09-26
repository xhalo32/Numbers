import Mathlib

variable {X : Type} {r : X → X → Prop}

-- ∀ (a, b), r a b → mk a = mk b

def Respects {Y : Type*} (r : X → X → Prop) (f : X → Y) := ∀ a b, r a b → f a = f b

#check Relation.EqvGen

def R := Set.Elem ({{x | Relation.EqvGen r a x} | a : X} : Set (Set X))

def mk : X → @R X r := fun x => ⟨({y | Relation.EqvGen r x y} : Set X), by simp⟩

-- Epimorphism universal property
#check Function.Surjective.right_cancellable
#check Function.RightInverse

#check Function.surjInv
#check Function.surjInv_eq

/-- Category-theoretical notion of choice:

All surjection have a section.
-/
theorem Function.Surjective.exists_rightInverse {X Y : Type*} {f : X → Y} (hf : f.Surjective) : ∃ (g : Y → X), RightInverse g f := by
  use surjInv hf
  apply Function.surjInv_eq

open Relation

theorem eqvGen_respects {Y : Type*} {f : X → Y} (hf : Respects r f) : Respects (EqvGen r) f := by
  intro a b hab
  induction hab with
  | rel a b h =>
    exact hf _ _ h
  | refl =>
    rfl
  | symm _ _ _ ih =>
    exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 =>
    exact ih1.trans ih2

theorem mk_surjective : Function.Surjective (@mk X r) := by
  sorry

theorem surjInv_mk {x : X} : (EqvGen r) (Function.surjInv (@mk_surjective X r) (mk x)) x := by
  sorry

-- R = X/r
theorem quot_exists_unique : ∃ R : Type, ∃ mk : X → R,
    -- Soundness
    (∀ (a b : X), r a b → mk a = mk b) ∧
    -- Coequalizer universal property
    (∀ {Y : Type} (f : X → Y), Respects r f → ∃! fext, fext ∘ mk = f) ∧
    -- Uniqueness
    (∀ (R' : Type) (mk' : X → R),
      (∀ (a b : X), r a b → mk a = mk b) →
      (∀ {Y : Type} (f : X → Y), Respects r f → ∃! fext, fext ∘ mk = f) →
      ∃ (h : R ≃ R'), True)
    := by
  use @R X r
  use @mk X r
  -- generalize (fun x => ⟨({y | Relation.EqvGen r x y} : Set X), ?_⟩) = mk
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    simp [R, mk]
    ext z
    simp
    constructor
    · intro haz
      apply Relation.EqvGen.symm
      apply Relation.EqvGen.trans (y := a)
      ·
        apply Relation.EqvGen.symm
        exact haz
      · apply Relation.EqvGen.rel
        exact hab
    ·
      intro hbz
      apply Relation.EqvGen.symm
      apply Relation.EqvGen.symm at hbz
      apply Relation.EqvGen.trans _ _ _ hbz
      apply Relation.EqvGen.symm
      apply Relation.EqvGen.rel
      exact hab
  · intro Y f hf
    have : Function.Surjective mk
    · sorry

    refine ⟨f ∘ Function.surjInv this, ?prop, ?unique⟩
    · ext x
      -- simp [mk]
      apply eqvGen_respects hf
      simp [surjInv_mk]


  sorry
