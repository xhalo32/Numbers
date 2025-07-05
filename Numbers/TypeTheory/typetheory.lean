import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.all false
open Real
universe u v

#check 0

#check π

#check Complex.I

#check (-1 : ℤ)

#check (-1 : ℝ)

#check (2/3 : ℚ)

#check (fun x ↦ sin x)

#check sin

#check ℝ

#check Type

#check Type 1

#check (1 + 1 = 2)

#check (1 + 1 = 3)

example : 641 = 641 := rfl

example : (fun x ↦ sin x) = (fun y ↦ sin y) := rfl

example : (fun x ↦ sin x) π = sin π := rfl

example : sin = (fun x ↦ sin x) := rfl

example : 1 + 1 = 2 := rfl

example (n : ℕ) : n + 0 = n := rfl

example (x : ℝ × ℝ) : x = ⟨x.1, x.2⟩ := rfl









-- FUNCTION TYPES

-- Formation rule

variable (A B C : Type u) (a : A) (b : B) (f : A → B)

#check A → B

-- Constructor

#check (fun (n : ℕ) ↦ n + 4)

#check (fun (n : ℕ) ↦ π)

example : ℕ → ℕ := by
  intro n
  exact 2 * n + n ^ 2

-- Eliminator

#check f a

-- Computation rule

example (a : ℝ) : (fun x ↦ sin x) a = sin a := rfl

-- Uniqueness principle

example : f = fun x ↦ f x := rfl

example (f g : A → B) (h : ∀ a, f a = g a) : f = g := by
  have hf : f = fun x ↦ f x := rfl
  have hg : g = fun x ↦ g x := rfl
  rw [hf, hg]
  sorry

open Prod

-- CARTESIAN PRODUCT

-- Formation rule

#check A × B

-- Constructor

#check (a, b)

-- Eliminator

variable (g : A → (B → C)) (x : A × B)

#check Prod.rec

#check (rec g x : C)

#check (rec g : A × B → C)


-- Computation rule

example (a : A) (b : B) : rec g (a, b) = g a b := rfl

-- Projections

#check (fst : A × B → A)

#check (fst x)

#check (snd : A × B → B)

#check (snd x)

example : (fst : A × B → A) = rec (fun a b ↦ a) := rfl

example : fst (a, b) = a := rfl

-- Uniqueness principle

example : x = (x.1, x.2) := rfl

lemma principle (f : A → B → C) : (rec f : A × B → C) = fun (x : A × B) ↦ f x.1 x.2 := rfl

lemma principle1 (f : A → B → C) : (rec f : A × B → C) = fun (x : A × B) ↦ f x.1 x.2 := by
  ext x
  rfl

lemma principle2 (f : A → B → C) : (rec f : A × B → C) = fun (x : A × B) ↦ f x.1 x.2 := by
  change (fun (t : A × B) ↦ (rec f : A × B → C) (t.1, t.2)) = _
  change (fun (t : A × B) ↦ f t.1 t.2) = _
  rfl

lemma principle3 (f : A × B → C) : f = fun (x : A × B) ↦ f (x.1, x.2) := rfl

lemma principle4 (f : A × B → C) : f = fun (x : A × B) ↦ f (x.1, x.2) := by
  change (fun t ↦ f t) = fun (x : A × B) ↦ f (x.1, x.2)
  change (fun t ↦ f t) = fun (x : A × B) ↦ f x
  rfl










#check (2 + 2 = 4)

#check (1 < 0)

#check Prop

def FLT := ∀ (n x y z), n > 2 → x^n+y^n=z^n → x*y*z=0

#check FLT

variable (P : Prop) (p : P)

#check p

#check Sort 0 --note that Lean automatically replace Sort 0 with Prop

variable (p₁ : 2 + 2 = 4) (p₂ : 2 + 2 = 5)

#check p₁

#check p₂

theorem easy : 1 + 1 = 2 := by rfl

#check easy

theorem FLT_theorem (n x y z : ℕ) (hn : n > 2) (H : x^n+y^n=z^n) : x*y*z = 0 := by sorry

variable (n x y z : ℕ) (hn : n > 2) (H : x^n+y^n=z^n)

#check FLT_theorem n x y z hn H

variable (C : Type v) (D : A → Type v)

#check (A → B)

#check (A → C)

#check (a : A) → D a

variable {A : Type*} (P : A → Prop)

example : ∀ n, n + 0 = n := by
  intro n
  rfl

#check (a : A) → P a

variable (A : Sort u) (B : A → Sort v)

#check (a : A) → B a

variable (P Q : Prop)

#check (A → Q)

#check (P → Q)

example : P → Q := by
  intro p
  sorry

example (p : P) (h : P → Q) : Q := by
  exact h p

example (p : P) (h : P → Q) : Q := by
  apply h
  exact p

#check (P ∧ Q)

variable (p : P) (q : Q)

#check (⟨p, q⟩: P ∧ Q)

example : P ∧ Q := by
  exact ⟨p, q⟩

example : P ∧ Q := by
  constructor
  · exact p
  · exact q

variable (A : Sort u) (f : P → Q → A)

#check And.elim f

example : And.elim f ⟨p, q⟩ = f p q := rfl

variable (t : P ∧ Q)

#check t.1

#check t.2

example : t = ⟨t.1, t.2⟩ := rfl

variable (h1 : P → Q)

#check (P ∨ Q)

#check Or.intro_left Q p

#check Or.intro_right P q

variable (R : Prop) (f : P → R) (g : Q → R) (t : P ∨ Q)

#check (Or.elim t f g)

example : Or.elim (Or.intro_left Q p) f g = f p := rfl

example : Or.elim (Or.intro_right P q) f g = g q := rfl

example (p : P) : P ∨ Q := by
  left
  exact p

example (q : Q) : P ∨ Q := by
  right
  exact q

example (R : Prop) (hP : P → R) (hQ : Q → R) (t : P ∨ Q) : R := by
  cases t with
  | inl p => apply hP
             exact p
  | inr q => apply hQ
             exact q

example (R : Prop) (hP : P → R) (hQ : Q → R) (t : P ∨ Q) : R := by
  cases t
  · apply hP
    assumption
  · apply hQ
    assumption

example (R : Prop) (hP : P → R) (hQ : Q → R) (t : P ∨ Q) : R := by
  rcases t with (p | q)
  · exact hP p
  · exact hQ q

#check True

example : True := by
  trivial

#check False

variable (A : Sort u) (p : False)

#check (False.elim p : A)

example (p : False) : FLT := by
  intro n x y z hn H
  exfalso
  exact p

example (p : False) : FLT := by
  cases p

variable (P : Prop)

#check ¬P

example : ¬P := by
  intro h
  sorry

variable (A : Sort u) (P : A → Prop)

#check (∃ a, P a)

variable (x : A) (h : P x)

#check (⟨x, h⟩ : ∃ a, P a)

example : ∃ n, n ^ 2 = 1 := by
  use 1
  simp

variable (Q : Prop) (h1 : ∃ a, P a) (h2 : ∀ a, P a → Q)

#check (Exists.elim h1 h2)

example (H : ∃ (x : ℝ), 2 = x^2) : (0 : ℝ) ≤ 2 := by
  obtain ⟨x, hx⟩ := H
  rw [hx]
  exact sq_nonneg x










/-- Our copy of the natural numbers called `N` -/
inductive N : Type where
| zero : N
| succ : N → N

namespace N

#check zero

#check succ

variable (n : N)

#check succ n

/-- This activate the notation `(0 : N)`. -/
instance : Zero N := ⟨zero⟩

theorem zero_def : zero = 0 := rfl

/-- Let's define `one` as `succ 0`. -/
def one : N := succ 0

/-- This activate the notation `(1 : N)`. -/
instance : One N := ⟨one⟩

theorem one_def : one = 1 := rfl

theorem one_eq_succ_zero : (1 : N) = succ 0 := rfl

variable (M : N → Sort u)

variable (z : M 0) (s : Π (n : N), M n → M (succ n))

#check (rec z s : Π (n : N), M n)
--here Lean is not smart enough to guess

#check (rec (motive := M) z s)
--one can help Lean writing `(motive := M)`

variable (n : N)

#check (rec (motive := M) z s n)

--ignore the `@`, it means that we want all the variables explicit
#check (@rec : Π (M : N → Sort u), M 0 → (Π (n : N), (M n → M (succ n))) → Π (n : N), M n)

variable (M : N → Sort u) (z : M 0)
  (s : Π (n : N), M n → M (succ n))

example : rec (motive := M) z s 0 = z := rfl

example (n : N) : rec (motive := M) z s (succ n) = s n (rec z s n) := rfl

variable (z : A) (s : N → A → A)

#check (rec (motive := fun _ ↦ A) z s)
--we say that the motive is the constant function `A`

#check (rec z s : N → A)
--or we can help Lean like this

example : rec z s 0 = z := rfl

example (n : N) : rec z s (succ n) = s n (rec z s n) := rfl

variable (M : N → Sort u) (z : M 0)
  (s : Π (n : N), M n → M (succ n))

noncomputable --ignore this
def F : Π (n : N), M n := rec z s

example (n : N) : F M z s (succ n) = s n (rec z s n) := rfl

def f1 : Π (n : N), M n
| 0 => z
| succ n => s n (f1 n)

example (n : N) : f1 M z s (succ n) = s n (f1 M z s n) := rfl

def add' : N → N → N
| 0 => id
| succ n => fun a ↦ succ (add' n a)

/- Pattern matching is smart enough to use several variables. -/
def add : N → N → N
| 0, a => a
| succ n, a => succ (add n a)

/- This activates the notation `a + b` for `add a b`. -/
instance : Add N := ⟨add⟩

/-The computation rules give us the following results for free.-/

theorem zero_add (a : N) : 0 + a = a := rfl

theorem succ_add (a b : N) : succ a + b = succ (a + b) := rfl

/- The following equality is not definitional! -/
theorem add_zero (a : N) : a + 0 = a := by
  revert a
  --the previous line is needed as `rec` only allows to build
  -- a dependent function "all at once", not a single value
  apply rec
  · exact zero_add 0
  · intro a ha
    rw [succ_add, ha]
    --We will see how `rw` works, it is related to the definition of `=`.

example : ∀ (a : N), a + 0 = a := by
  intro a
  induction a with
  | zero => rfl
  | succ d hd => --here one can replace `succ` by `_`,
                --no need to know the name of the consuctor
    rw [succ_add, hd]

theorem add_succ (a b : N) : a + (succ b) = succ (a + b) := by
  induction a with
  | zero => rfl
  | _ d hd =>
    rw [succ_add, hd]
    rfl

theorem succ_eq_add_one (a : N) : succ a = a + 1 := by
  rw [one_eq_succ_zero, add_succ, add_zero]

theorem add_comm (a b : N) : a + b = b + a := by
  induction a with
  | zero => rw [zero_def, zero_add, add_zero]
  | _ d hd =>
    rw [succ_add, hd, add_succ]

theorem one_add_eq_succ (a : N) : 1 + a = succ a := by
  rw [add_comm, succ_eq_add_one]

theorem add_assoc (a b c : N) : a + b + c = a + (b + c) := by
  induction a with
  | zero => rw [zero_def, zero_add, zero_add]
  | _ d hd => rw [succ_add, succ_add, hd, succ_add]

def pred : N → N
| 0 => 0
| succ n => n

theorem pred_succ (n : N) : pred (succ n) = n := rfl

theorem pred_zero : pred 0 = 0 := rfl

theorem succ_inj (a b : N) (h : succ a = succ b) : a = b := by
  have H : pred (succ a) = pred (succ b) := by
    rw [h]
  rw [pred_succ, pred_succ] at H
  exact H

theorem true_ne_false : True ≠ False := by
  intro h
  rw [← h]
  trivial

theorem zero_ne_one : (0 : N) ≠ 1 := by
  show 0 = 1 → False
  --this worked because it is a reformulation of the goal
  intro h
  let f : N → Prop :=
    N.rec False (fun a b => True)
  have hzero : f 0 = False := rfl
  have hone : f 1 = True := rfl
  rw [h, hone] at hzero
  exact true_ne_false hzero

theorem succ_ne_zero (n : N) : succ n ≠ 0 := by
  intro h
  let f : N → Prop :=
    N.rec False (fun a b => True)
  have hzero : f 0 = False := rfl
  have hn : f (succ n) = True := rfl
  rw [← h, hn] at hzero
  exact true_ne_false hzero

example : ¬(∃ (n : N), succ n = 0) := by
  rintro ⟨n, hn⟩
  --this is the same as `intro n` followed by `obtain ⟨n, hn⟩ := h`
  exact succ_ne_zero n hn

theorem succ_ne_of_ne (a b : N) (h : a ≠ b) : succ a ≠ succ b :=
  fun hsucc ↦ h (succ_inj _ _ hsucc)

end N










example (P : Prop) (p q : P) : p = q := rfl

example (p : ∀ (n : N), 0 + n = n) : p = N.zero_add := rfl

namespace Example

variable (A : Type)

inductive Inhabited (A : Type) : Type
| intro (val : A) : Inhabited A

inductive Nonempty (A : Type) : Prop
| intro (val : A) : Nonempty A

namespace Inhabited

variable (A : Type) (a : A) (B : Sort u) (f : A → B)

#check Inhabited A

#check (⟨a⟩ : Inhabited A)

#check (rec f : Inhabited A → B)

example : rec f ⟨a⟩ = f a := rfl

noncomputable
example (g : A → N) : Inhabited A → N := rec g

noncomputable
def default : Inhabited A → A := rec (fun (x : A) ↦ x)

example : default A ⟨a⟩ = a := rfl

end Inhabited

namespace Nonempty

variable (A : Type) (a : A) (P : Prop) (f : A → P)

#check Nonempty A

#check (⟨a⟩ : Nonempty A)

#check (rec f : Nonempty A → P)

-- The following is a consequence of proof irrelevance.
example : rec f ⟨a⟩ = f a := rfl

example (elim : Π (B : Type), (N → B) → (Nonempty N → B))
    (H : ∀ (B : Type) (n : N) (f : N → B), elim B f ⟨n⟩ = f n) : False := by
  let default := elim N id
  let h0 := (⟨0⟩ : Nonempty N)
  let h1 := (⟨1⟩ : Nonempty N)
  have hdefault : default h0 = default h1 := rfl
  have hdefault0 : default h0 = 0 := H N 0 id
  have hdefault1 : default h1 = 1 := H N 1 id
  apply N.zero_ne_one
  rewrite [← hdefault0, ← hdefault1] --here `rw` automatically tries `rfl` and finishes the proof
  exact hdefault

#check rec

#check Inhabited.rec

end Nonempty

end Example










open N Function

namespace ex

inductive Eq {A : Sort u} : A → A → Prop
| refl (a : A) : Eq a a

open Eq

infix:50 " ≃ "  => Eq

#check @Eq.rec

variable (A : Sort u) (a b : A) (h : a ≃ b)

#check @Eq.rec A a

variable (P : A → Prop) (ha : P a)

#check @Eq.rec A a (fun b _ ↦ P b)

#check @Eq.rec A a (fun b _ ↦ P b) ha b h

variable (A : Sort u)

lemma reflexivity (a : A) : a ≃ a := by
  exact refl a

lemma symmetry (a b : A) (h : a ≃ b) : b ≃ a := by
  let P : A → Prop := fun x ↦ x ≃ a
  exact Eq.rec (motive := fun x _ ↦ P x) (reflexivity A a) h

lemma transitivity (a b c : A) (hab : a ≃ b) (hbc : b ≃ c) : a ≃ c := by
  let P : A → Prop := fun x ↦ a ≃ x
  exact Eq.rec (motive := fun x _ ↦ P x) hab hbc

variable {A : Type*}

lemma substitution (B : Type v) (f : A → B) (a b : A) (h : a ≃ b) :
    f a ≃ f b := by
  let P : A → Prop := fun x ↦ f a ≃ f x
  exact Eq.rec (motive := fun x _ ↦ P x) (reflexivity B (f a)) h

example (R : A → A → Prop) (hrefl : ∀ a, R a a) (a b : A) (h : a ≃ b) : R a b := by
  let P : A → Prop := fun x ↦ R a x
  exact Eq.rec (motive := fun x _ ↦ P x) (hrefl a) h

example : ∀ (x : N), x ≃ x + 0  := by
  apply N.rec
  · exact Eq.refl _
  · intro d h
    have : succ (d + 0) ≃ succ d + 0 := Eq.refl _
    refine transitivity _ _ _ _ ?_ this
    apply substitution
    exact h

example : ∀ (x : N), x ≃ x + 0  := by
  apply N.rec
  · exact Eq.refl 0
  · intro d h
    have : succ d + 0 ≃ succ (d + 0) := Eq.refl _
    refine Eq.rec (motive := fun n _ ↦ succ d ≃ n) ?_ this
    exact Eq.rec (motive := fun n _ ↦ succ d ≃ succ n) (Eq.refl _) h

end ex

#check propext

example (P : Prop) (p : P) : P = True := by
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact p

example (P : Prop) (np : ¬P) : P = False := by
  apply propext
  constructor
  · intro hP
    exact np hP
  · intro h
    exact False.rec _ h

example : (∀ (n : N), n + 0 = n) = True := by
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact N.add_zero

example : (∀ (n : N), n + 0 = n) = (0 < π) := by
  apply propext
  constructor
  · intro _
    exact Real.pi_pos
  · intro _
    exact N.add_zero

example : (3 < 2) = False := by
  apply propext
  constructor
  · intro h
    linarith
  · intro h
    exact False.rec _ h

#check Quot

#check Quot.mk

#check Quot.ind

example (A : Sort u) (R : A → A → Prop) (x : Quot R) :
    ∃ a, Quot.mk R a = x := by
  revert x
  apply Quot.ind
  intro a
  use a

#check Quot.lift

#check Quot.sound

example (A : Sort u) (B : Sort v) (R : A → A → Prop) (f : A → B)
    (H : ∀ a b, R a b → f a = f b) (a : A) :
    Quot.lift f H (Quot.mk R a) = f a := rfl

example (A : Sort u) : Nonempty A ↔ ∃ (_ : A), True := by
  constructor
  · rintro ⟨a⟩
    use a
  · rintro ⟨a, _⟩
    exact ⟨a⟩

#check Classical.choice

example (I : Sort u) (f : I → Sort v) (H : ∀ i, Nonempty (f i)) :
    Nonempty (Π (i : I), f i) := by
  constructor
  intro i
  exact Classical.choice (H i)

example (P : Prop) : P = True ∨ P = False := by
  cases em P with
  | inl h =>
    left
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      exact h
  | inr h =>
    right
    apply propext
    constructor
    · exact h
    · intro H
      exact False.rec _ H

example (P : Prop) : ¬¬P → P := by
  intro H
  cases em P with
  | inl h =>
    exact h
  | inr h =>
    exfalso
    exact H h

example (P Q : Prop) (h : P → Q) (h' : ¬P → Q) : Q := by
  cases em P with
  | inl hP =>
    exact h hP
  | inr hnP =>
    exact h' hnP

example (P Q : Prop) (h : P → Q) (h' : ¬P → Q) : Q := by
  by_cases hP : P
  · exact h hP
  · exact h' hP

example : ∀ (P : Prop), P ∨ ¬P := by
  by_contra! h
  obtain ⟨P, hP⟩ := h
  exact hP.1 hP.2
