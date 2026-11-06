module

public import AnalyticESC.Basic

@[expose] public section

/-!
# Real-variable and identity-theorem lemmas

Lemma 3.1 (closeness of two functions gives closeness of their derivatives), its iterate, the
identity theorem on `B_ε` in the forms used in the paper, and the elementary bound (4.3).
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## Lemma 3.1 and its iterate -/

/-- Taylor's theorem of order two with the Lagrange remainder, for a smooth map on an open set
containing the segment between `x` and `y`. -/
private theorem exists_taylor_two {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ⊤ f U) {x y : ℝ} (hxy : x ≠ y) (hsub : uIcc x y ⊆ U) :
    ∃ ξ ∈ uIoo x y, f y - f x - deriv f x * (y - x) = deriv (deriv f) ξ * (y - x) ^ 2 / 2 := by
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy
    ((hf.mono hsub).of_le le_top)
  refine ⟨ξ, hξ, ?_⟩
  have hd : derivWithin f (uIcc x y) x = deriv f x :=
    ((hf.contDiffAt (hU.mem_nhds (hsub left_mem_uIcc))).differentiableAt (by decide)).derivWithin
      (uniqueDiffOn_uIcc hxy x left_mem_uIcc)
  simp [hd] at h
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [← h]
  ring

/-- Lemma 3.1 for smooth maps on a neighbourhood of `J = [a, b]`, with any common bound `Q` for the
second derivatives. -/
theorem abs_deriv_sub_le_of_abs_sub_le {f g : ℝ → ℝ} {a b η Q : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ⊤ f U) (hg : ContDiffOn ℝ ⊤ g U) (hη : 0 < η)
    (hJ : 2 * Real.sqrt η < b - a) (hfQ : ∀ x ∈ Icc a b, |deriv (deriv f) x| ≤ Q)
    (hgQ : ∀ x ∈ Icc a b, |deriv (deriv g) x| ≤ Q) (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ η) :
    ∀ x ∈ Icc a b, |deriv f x - deriv g x| ≤ (2 + Q) * Real.sqrt η := by
  intro x hx
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hs2 : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
  -- One of `x ± √η` lies in `[a, b]`.
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Icc a b, |y - x| = Real.sqrt η := by
    by_cases h : x + Real.sqrt η ≤ b
    · exact ⟨x + Real.sqrt η, ⟨by linarith [hx.1], h⟩, by simp [abs_of_pos hs]⟩
    · refine ⟨x - Real.sqrt η, ⟨by linarith, by linarith [hx.2]⟩, ?_⟩
      rw [show x - Real.sqrt η - x = -Real.sqrt η by ring, abs_neg, abs_of_pos hs]
  have hxy : x ≠ y := by rintro rfl; rw [sub_self, abs_zero] at hyx; exact hs.ne hyx
  have hsub : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
  obtain ⟨ξ₁, hξ₁, h₁⟩ := exists_taylor_two hU hf hxy (hsub.trans hab)
  obtain ⟨ξ₂, hξ₂, h₂⟩ := exists_taylor_two hU hg hxy (hsub.trans hab)
  have hd2 : (y - x) ^ 2 = η := by rw [← sq_abs, hyx, hs2]
  have key : (deriv f x - deriv g x) * (y - x) = (f y - g y) - (f x - g x) -
      (deriv (deriv f) ξ₁ - deriv (deriv g) ξ₂) * (y - x) ^ 2 / 2 := by
    linear_combination h₂ - h₁
  have hb : |deriv (deriv f) ξ₁ - deriv (deriv g) ξ₂| ≤ 2 * Q := by
    linarith [abs_sub (deriv (deriv f) ξ₁) (deriv (deriv g) ξ₂),
      hfQ ξ₁ (hsub (Ioo_subset_Icc_self hξ₁)), hgQ ξ₂ (hsub (Ioo_subset_Icc_self hξ₂))]
  refine le_of_mul_le_mul_right ?_ hs
  rw [← hyx, ← abs_mul, key, hd2, hyx, mul_assoc, ← sq, hs2]
  have e3 : |(deriv (deriv f) ξ₁ - deriv (deriv g) ξ₂) * η / 2| ≤ Q * η := by
    rw [abs_div, abs_mul, abs_of_pos hη, abs_two]; nlinarith
  linarith [abs_sub (f y - g y - (f x - g x))
    ((deriv (deriv f) ξ₁ - deriv (deriv g) ξ₂) * η / 2),
    abs_sub (f y - g y) (f x - g x), hfg x hx, hfg y hy]

/-- The `j`-th derivative of a smooth map on an open set is smooth there. -/
private theorem contDiffOn_iteratedDeriv_of_isOpen {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ⊤ f U) (j : ℕ) :
    ContDiffOn ℝ ⊤ (iteratedDeriv j f) U := by
  induction j with
  | zero => simpa using hf
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv_of_isOpen hU le_top

/-- Lemma 3.1 iterated `k` times: closeness `η ≤ 1` of `f` and `g` gives closeness
`(2 + Q)² η^{2^{-k}}` of their `k`-th derivatives, given bounds `Q` on the derivatives of order
at most `k + 1`. -/
theorem abs_iteratedDeriv_sub_le {f g : ℝ → ℝ} {a b η Q : ℝ} {U : Set ℝ} (k : ℕ) (hU : IsOpen U)
    (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ⊤ f U) (hg : ContDiffOn ℝ ⊤ g U)
    (hη : 0 < η) (hη1 : η ≤ 1) (hQ : 0 ≤ Q)
    (hfQ : ∀ j ≤ k + 1, ∀ x ∈ Icc a b, |iteratedDeriv j f x| ≤ Q)
    (hgQ : ∀ j ≤ k + 1, ∀ x ∈ Icc a b, |iteratedDeriv j g x| ≤ Q)
    (hJ : 2 * (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ k) < b - a) (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ η) :
    ∀ x ∈ Icc a b, |iteratedDeriv k f x - iteratedDeriv k g x| ≤ (2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ k) :=
  by
  have h2Q : 1 ≤ (2 + Q) ^ 2 := by nlinarith
  suffices H : ∀ j ≤ k, ∀ x ∈ Icc a b,
      |iteratedDeriv j f x - iteratedDeriv j g x| ≤ (2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ j) from
    H k le_rfl
  intro j
  induction j with
  | zero =>
    intro _ x hx
    simp only [iteratedDeriv_zero, pow_zero, Real.rpow_one]
    nlinarith [hfg x hx]
  | succ j ih =>
    intro hjk x hx
    have hsqrt : Real.sqrt ((2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ j)) =
        (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ (j + 1)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hη.le, pow_succ, one_div]
    have hexp : η ^ ((2 : ℝ)⁻¹ ^ (j + 1)) ≤ η ^ ((2 : ℝ)⁻¹ ^ k) :=
      Real.rpow_le_rpow_of_exponent_ge hη hη1
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hjk)
    have hdd (φ : ℝ → ℝ) : deriv (deriv (iteratedDeriv j φ)) = iteratedDeriv (j + 2) φ := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have key := abs_deriv_sub_le_of_abs_sub_le hU hab
      (contDiffOn_iteratedDeriv_of_isOpen hU hf j)
      (contDiffOn_iteratedDeriv_of_isOpen hU hg j)
      (mul_pos (by positivity) (Real.rpow_pos_of_pos hη _)) (by rw [hsqrt]; nlinarith)
      (fun y hy => by rw [hdd]; exact hfQ (j + 2) (by omega) y hy)
      (fun y hy => by rw [hdd]; exact hgQ (j + 2) (by omega) y hy)
      (ih (by omega)) x hx
    rw [hsqrt, ← iteratedDeriv_succ, ← iteratedDeriv_succ] at key
    exact key.trans_eq (by ring)

/-! ## The identity theorem on `B_ε` -/

/-- The inclusion `ℝ → ℂ` maps punctured neighbourhoods into punctured neighbourhoods. -/
private theorem tendsto_ofReal_nhdsNE (c : ℝ) :
    Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] c) (𝓝[≠] (c : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa using hx

/-- Identity theorem: maps holomorphic on `B_ε` that agree on a nondegenerate interval of `I`
agree on `B_ε`. -/
theorem eqOn_nbhd_of_eqOn_Icc {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {a b : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ I) (heq : ∀ x ∈ Icc a b, g x = h x) : EqOn g h (nbhd ε) :=
  (hg.analyticOnNhd (isOpen_nbhd ε)).eqOn_of_preconnected_of_frequently_eq
    (hh.analyticOnNhd (isOpen_nbhd ε)) (isPreconnected_nbhd ε)
    (ofReal_mem_nbhd hε (hI ⟨by linarith, by linarith⟩))
    ((tendsto_ofReal_nhdsNE ((a + b) / 2)).frequently
      ((eventually_nhdsWithin_of_eventually_nhds
        (Icc_mem_nhds (by linarith) (by linarith))).frequently.mono heq))

/-- Identity theorem: maps holomorphic on `B_ε` with all derivatives equal at a point of `I`
agree on `B_ε`. -/
theorem eqOn_nbhd_of_iteratedDeriv_eq {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {x : ℝ} (hx : x ∈ I)
    (heq : ∀ k, iteratedDeriv k g x = iteratedDeriv k h x) : EqOn g h (nbhd ε) := by
  have hU := isOpen_nbhd ε
  have hball : ball (x : ℂ) ε ⊆ nbhd ε := ball_subset_nbhd hx
  refine (hg.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hh.analyticOnNhd hU)
    (isPreconnected_nbhd ε) (ofReal_mem_nbhd hε hx) ?_
  filter_upwards [ball_mem_nhds (x : ℂ) hε] with z hz
  rw [← Complex.taylorSeries_eq_on_ball' hz (hg.mono hball),
    ← Complex.taylorSeries_eq_on_ball' hz (hh.mono hball)]
  simp_rw [heq]

/-- A map analytic at every point of `I`, not identically zero on `I`, has finitely many zeros
in `I`. -/
theorem finite_zeros_of_analyticAt {g : ℂ → ℂ} (hg : ∀ x ∈ I, AnalyticAt ℂ g x)
    (hne : ∃ x ∈ I, g x ≠ 0) : {x : ℝ | x ∈ I ∧ g x = 0}.Finite := by
  by_contra hinf
  obtain ⟨c, hcI, hacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc fun _ hx => hx.1
  have han : AnalyticOnNhd ℂ g (((↑) : ℝ → ℂ) '' I) := by rintro _ ⟨x, hx, rfl⟩; exact hg x hx
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn) (mem_image_of_mem _ hcI)
    ((tendsto_ofReal_nhdsNE c).frequently
      ((accPt_iff_frequently_nhdsNE.1 hacc).mono fun _ hx => hx.2))
  obtain ⟨x, hx, hgx⟩ := hne
  exact hgx (hzero (mem_image_of_mem _ hx))

/-- A map holomorphic on `B_ε`, not identically zero on `I`, has finitely many zeros in `I`. -/
theorem finite_zeros {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (nbhd ε))
    (hne : ∃ x ∈ I, g x ≠ 0) : {x : ℝ | x ∈ I ∧ g x = 0}.Finite :=
  finite_zeros_of_analyticAt
    (fun _ hx => hg.analyticAt ((isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd hε hx))) hne

end AnalyticESC
