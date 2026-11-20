module

public import DOZZ.GMC.SharpMoments.InverseGamma
public import DOZZ.GMC.Annulus.HigherScales

/-! # Coupling comparison for convex cutoff moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- At fine cutoffs, a single reference-disk positive moment bound works for every coupling
in a compact family below its critical moment threshold. -/
theorem regularizedGMC_reference_positive_moment_compact_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓpos : ∀ γ ∈ Γ, 0 < γ)
    (p : ℝ) (hp : 1 < p) (hcrit : ∀ γ ∈ Γ, p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Γ, ∀ r : ℝ, 1 ≤ r →
      (∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 8))) ^ p ∂P) ≤ C := by
  classical
  rcases Set.eq_empty_or_nonempty Γ with hEmpty | hNonempty
  · refine ⟨0, by simp, ?_⟩
    simp [hEmpty]
  obtain ⟨g, hg, hmax⟩ := hΓ.exists_isMaxOn hNonempty continuousOn_id
  obtain ⟨C, hC, hbound⟩ := regularizedGMC_reference_positive_moment_uniform
    P X hX Xc hXc g p (hΓpos g hg) hp (hcrit g hg)
    (R := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro γ hγ r hr
  have hcmp := regularizedGMC_convex_moment_le_of_gamma_le P X hX Xc hXc P X hX Xc hXc γ g r
    (hΓpos γ hγ) (hmax hγ) (Metric.ball 0 (1 / 8)) Metric.isOpen_ball.measurableSet
    (fun x hx y hy => circleField_covariance_nonneg_reference P X hX Xc hXc r hr x hx y hy)
    p (Or.inr hp.le)
  exact hcmp.trans (hbound r (by linarith))

end DOZZ.Proofs
