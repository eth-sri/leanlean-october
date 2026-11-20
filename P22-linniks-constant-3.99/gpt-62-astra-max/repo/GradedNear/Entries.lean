module

public import GradedNear.Gram

/-!
# Bounds for the Gram entries

* principal entries (same character) from [X, Lemma 3.1]:
  `𝓛⁻¹ Re primeSum(1, g, s) ≤ Re G((s - 1)𝓛) + ε`;
* non-principal entries (distinct characters) from [X, Lemma 3.2], when no zero of the
  quotient `L`-function in the local disc lies to the right of `s`: `≤ g(0)/6 + ε`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

open Filter

lemma loglog_atTop : Tendsto (fun q : ℕ => Real.log (Real.log q)) atTop atTop :=
  Real.tendsto_log_atTop.comp log_level_atTop

/-- The points with bounded normalized displacement eventually lie in the explicit-formula region. -/
lemma eventually_region (K : ℝ) : ∀ᶠ q : ℕ in atTop, 0 < Real.log q ∧
    ∀ σ γ, |σ| ≤ K → |γ| ≤ Real.log q → LemmaRegion q (point q σ γ) := by
  filter_upwards [(Real.tendsto_sqrt_atTop.comp loglog_atTop).eventually_ge_atTop K,
    eventually_ge_atTop 2] with q hK hq
  have hℓ := log_q_pos hq
  refine ⟨hℓ, fun σ γ hσ hγ => ⟨?_, by simpa only [point_im] using hγ⟩⟩
  simp only [point_re, sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos hℓ]
  exact div_le_div_of_nonneg_right (hσ.trans hK) hℓ.le

/-- Normalized principal entries, uniformly in the explicit-formula region. -/
lemma principal_entry (hX31 : XylourisLemma31) {g : ℝ → ℝ} {xg Bg ε : ℝ}
    (hg : Condition1 g xg Bg) (hε : 0 < ε) : ∀ᶠ q : ℕ in atTop, ∀ s, LemmaRegion q s →
      (primeSum (1 : DirichletCharacter ℂ q) g s).re / Real.log q ≤
        (laplace g ((s - 1) * (Real.log q : ℂ))).re + ε := by
  obtain ⟨C, q₀, hC⟩ := hX31 _ _ _ hg
  filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 2,
    (loglog_atTop.const_div_atTop C).eventually_lt_const hε] with q hq hq2 hsmall s hs
  have hℓ := log_q_pos hq2
  have h := (re_le_norm _).trans (hC q hq s hs)
  rw [sub_re, re_ofReal_mul, mul_div_right_comm] at h
  rw [div_le_iff₀ hℓ]
  linarith [mul_lt_mul_of_pos_right hsmall hℓ]

/-- A zero sum is nonnegative when all its zeros lie left of the test point. -/
lemma zeroSum_nonneg {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {g : ℝ → ℝ}
    (hg : Condition2 g) {s : ℂ} {δ : ℝ} (hz : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
      inDisc[s.im,δ] ρ → ρ.re ≤ s.re) : 0 ≤ zeroSum χ g s δ := by
  refine finsum_nonneg fun ρ => finsum_nonneg fun hρ => mul_nonneg (Nat.cast_nonneg _) (hg.re_nonneg _ ?_)
  simpa only [re_mul_ofReal, sub_re] using mul_nonneg (sub_nonneg.mpr (hz ρ hρ.2 hρ.1)) (Real.log_natCast_nonneg q)

end GradedNear
