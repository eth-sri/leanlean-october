module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaCutoffEstimates

@[expose] public section

/-!
# Globally smooth corrections for actual Legendre phases

The correction uses the genuine anchored dual error on the cutoff support.
Its smoothness and all fixed-order uniform bounds are derived from the
original approximate-model hypothesis, not stipulated for an extension.
-/



open Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025


section
variable {σ δ w v : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hp : 0 < v)
include σ δ w v F hσ hδ hF hv hp

theorem anchoredLegendreError_contDiffAt
     :
    ContDiffAt ℝ ∞ (anchoredLegendreError F σ w) v :=
  ((modelPhaseLegendreDual_contDiffAt hσ hδ hF hv).sub
    (referenceModelPrimitive_contDiffAt σ⁻¹ hp)).sub contDiffAt_const

theorem anchoredLegendreError_iteratedDeriv
     (n : ℕ) :
    iteratedDeriv (n+1) (anchoredLegendreError F σ w) v =
      iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
        iteratedDeriv n (modelPhase σ⁻¹) v := by
  have hN : ((n+1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1)
  have hG := (modelPhaseLegendreDual_contDiffAt hσ hδ hF hv).of_le hN
  have hR := (referenceModelPrimitive_contDiffAt σ⁻¹ hp).of_le hN
  unfold anchoredLegendreError
  rw [iteratedDeriv_fun_sub (hG.sub hR) contDiffAt_const,
    iteratedDeriv_fun_sub hG hR, referenceModelPrimitive_iteratedDeriv σ⁻¹ hp n]
  simp [iteratedDeriv_const]
end



