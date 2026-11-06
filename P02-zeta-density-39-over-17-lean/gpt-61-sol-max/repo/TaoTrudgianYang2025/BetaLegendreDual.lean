module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaSlopeInverse

@[expose] public section

/-!
# Sign-normalized Legendre dual of an actual model phase

The dual is v*u-F(u), where F'(u)=v. It is smooth on the actual slope
image and has negative reciprocal curvature. The stationary-phase exponent
F(u)-v*u has the opposite sign; the identity below records that convention.
This does not yet prove the B-process exponential-sum transformation.
-/

noncomputable section

open Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025


def modelPhaseLegendreDual (F : ℝ → ℝ) (v : ℝ) : ℝ :=
  v * modelPhaseInverseSlope F v - F (modelPhaseInverseSlope F v)

section
variable {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
include σ δ F hσ hδ hF v hv

theorem modelPhaseLegendreDual_contDiffAt  :
    ContDiffAt ℝ ∞ (modelPhaseLegendreDual F) v := by
  have hi := modelPhaseInverseSlope_contDiffAt hσ hδ hF hv
  exact (contDiffAt_id.mul hi).sub
    ((approximateModelPhase_contDiffAt hF (modelPhaseInverseSlope_mem hv)).comp v hi)

theorem modelPhaseLegendreDual_hasDerivAt  :
    HasDerivAt (modelPhaseLegendreDual F) (modelPhaseInverseSlope F v) v := by
  have hi := (modelPhaseInverseSlope_hasStrictDerivAt hσ hδ hF hv).hasDerivAt
  have hf := (approximateModelPhase_contDiffAt hF (modelPhaseInverseSlope_mem hv)).differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  convert ((hasDerivAt_id v).mul hi).sub (hf.hasDerivAt.comp v hi) using 1
  · rfl
  · rw [deriv_modelPhaseInverseSlope_apply hv, id_eq]
    ring

theorem deriv_modelPhaseLegendreDual  :
    deriv (modelPhaseLegendreDual F) v = modelPhaseInverseSlope F v :=
  (modelPhaseLegendreDual_hasDerivAt hσ hδ hF hv).deriv
end



