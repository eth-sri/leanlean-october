module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaModelJetEstimatesFull

@[expose] public section

/-!
# Uniform bounds for the actual inverse-derivative jet coordinates

The magnitude and error constants depend only on sigma and the finite
coordinate index. They are derived from the original model-phase errors.
-/

noncomputable section

open Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025


def inverseJetMagnitude (σ : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => (modelPhaseCurvatureLower σ)⁻¹
  | n+2 => modelPhaseJetCoefficient σ (n+1)+1

theorem inverseJetMagnitude_nonneg {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    0 ≤ inverseJetMagnitude σ j := by
  have hc := (modelPhaseCurvatureLower_pos hσ).le
  match j with
  | 0 => norm_num [inverseJetMagnitude]
  | 1 => exact inv_nonneg.mpr hc
  | n+2 => exact add_nonneg (modelPhaseJetCoefficient_nonneg σ (n+1)) zero_le_one

theorem modelPhaseInverseJet_abs_le
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (j : ℕ) (hj : j ≤ P) :
    |modelPhaseInverseJet F v j| ≤ inverseJetMagnitude σ j := by
  have hu := modelPhaseInverseSlope_mem hv
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  match j with
  | 0 =>
      change |modelPhaseInverseSlope F v| ≤ 2
      rw [abs_of_pos (zero_lt_one.trans hu.1)]
      exact hu.2.le
  | 1 =>
      have hb := (approximateModelPhase_curvature_deriv_bounds hσ hδ hF₁ hu).1
      have hc := modelPhaseCurvatureLower_pos hσ
      have hn : deriv (deriv F) (modelPhaseInverseSlope F v) < 0 := by linarith
      change |(deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹| ≤
        (modelPhaseCurvatureLower σ)⁻¹
      rw [abs_inv, abs_of_neg hn]
      exact inv_anti₀ hc hb
  | n+2 =>
      have hp : n+1 ≤ P := by omega
      have he := approximateModelPhase_iteratedDeriv_error hF hu (n+1) hp
      have hb := iteratedDeriv_modelPhase_abs_le hσ.le hu (n+1)
      have ht := abs_add_le
        (iteratedDeriv (n+2) F (modelPhaseInverseSlope F v) -
          iteratedDeriv (n+1) (modelPhase σ) (modelPhaseInverseSlope F v))
        (iteratedDeriv (n+1) (modelPhase σ) (modelPhaseInverseSlope F v))
      rw [sub_add_cancel] at ht
      change |iteratedDeriv (n+2) F (modelPhaseInverseSlope F v)| ≤
        modelPhaseJetCoefficient σ (n+1)+1
      have hd : δ ≤ 1 := hδ.trans (min_le_right _ _)
      linarith


