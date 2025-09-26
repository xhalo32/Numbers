import Numbers.RealsOrder

open MyPrereal

namespace MyReal

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

-- Original had + 1 for some reason
-- lemma archimedean (x : MyReal) : ∃ (n : ℕ), x ≤ k (MyRat.i (n + 1)) := by
lemma archimedean (x : MyReal) : ∃ (n : ℕ), x ≤ k (MyRat.i n) := by
  rcases le_or_gt x 0 with h | h
  · use 0
    grw [h, ← k_zero]
    rw [k_le_iff]
    simp
  ·
    -- choose a rational number > x
    obtain ⟨r, hr⟩ := myRat_dense_rat (2 * x) h
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

lemma natCast_eq {n : ℕ} : (n : MyReal) = k (MyRat.i n) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp [ih, k_add]

instance : Archimedean MyReal := by
  rw [archimedean_iff_nat_le]
  simp_rw [natCast_eq]
  intro x
  exact archimedean x

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
  · rw [inv_nonneg]
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

#printaxioms complete

end completeness

-- We already have lattice structure
#synth Lattice MyReal

-- But don't have ⨆ or ⨅

open MyRat in
lemma intCast_eq {n : ℤ} : (n : MyReal) = k (j n) := by
  cases n with
  | ofNat n =>
    induction n with
    | zero =>
      simp [j_zero]
    | succ n ih =>
      simp at ih
      simp [ih, j_add, j_one, k_add]
  | negSucc n =>
    induction n with
    | zero =>
      simp [j_neg, j_one]
    | succ n ih =>
      simp at ih
      simp [ih, j_neg, j_add, j_one, k_add]

noncomputable instance : FloorRing MyReal :=
  Archimedean.floorRing _

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

end MyReal
