module

public import DOZZ.GMC.WeightedCutoff.CoarseMoment

/-! # Uniform bounded-disk moments at coarse physical cutoffs -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem regularizedGMC_bounded_ball_moment_coarse_uniform_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    (q : ℝ) (hq : 1 < q) B r₀ (hB : 0 ≤ B) (hr₀ : 0 < r₀) :
    ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ δ : ℝ,
      1 / 8 ≤ δ → δ ≤ r₀ →
      (∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball 0 B)) ^ q ∂P) ≤ D := by
  let V : ℝ := Real.log 8 + 2 * Real.log (1 + B + r₀)
  have hV : 0 ≤ V := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)
    have := Real.log_nonneg (show 1 ≤ 1 + B + r₀ by linarith)
    dsimp [V]
    positivity
  refine ⟨(gmcReferenceMeasure (Metric.ball (0 : ℂ) B) ^ q * ENNReal.ofReal (Real.exp (4 * (q ^ 2 - q) / 2 * V))), (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith) (ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))))) ENNReal.ofReal_lt_top), ?_⟩
  intro γ hγ hγ2 δ hδa hδr
  let r := Real.log (1 / δ)
  have hrT : r ≤ Real.log 8 := by
    apply Real.log_le_log (by positivity)
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hcut : Real.exp (-r) = δ := by
    dsimp [r]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  apply (regularizedGMC_moment_upper_of_variance_bound P X hX Xc hXc γ r q V hq.le (Metric.ball 0 B) Metric.isOpen_ball.measurableSet (by intro x hx; exact gmcCircle_variance_le_bounded_radius P X hX Xc hXc B r₀ (Real.log 8) r hB hr₀.le hrT (by rw [hcut]; exact hδr) x (le_of_lt (by simpa using hx)))).trans
  apply mul_le_mul_right
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right (show γ ^ 2 ≤ 4 by nlinarith) (mul_nonneg (by nlinarith) hV : 0 ≤ (q ^ 2 - q) / 2 * V)]))

end DOZZ.Proofs
