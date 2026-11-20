/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.UnreflectedD
public import DOZZ.FourPoint.Diagonal.Assembly

/-! The unreflected formula follows from the diagonal classification and the first shift. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- **The unreflected `γ/2` formula** ([KRV, Theorem 9.1]). -/
theorem gammaHalf_full_unreflected_formula {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hαlo : γ / 2 < α₁) (hαhi : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
    let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
    let c := gaussParameterC γ (γ / 2) α₁
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
            ‖gaussFMinus H a b c z‖ ^ 2 +
          (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
            structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
              ‖gaussFPlus H a b c z‖ ^ 2 := by
  have hdiag (M' : Ω → Measure ℂ) (γ' t : ℝ) (h0 : 0 < γ') (h2 : γ' < 2)
      (hM' : IsGMCOf P X γ' M') (_ : γ' / 2 < t) (hhi : t < 2 / γ') (h₂ : α₂ < Q γ')
      (h₃ : α₃ < Q γ') (hs' : 2 * Q γ' + γ' / 2 < t + α₂ + α₃) :
      HasGammaHalfDiagonal H P M' γ' μ t α₂ α₃ :=
    degenerateFourPoint_diagonal_classification hH P X M' γ' μ (γ' / 2) t α₂ α₃ h0 h2 hμ
      (Or.inl rfl) (by unfold Q; linarith) h₂ h₃ hs' hX hM'
  have hshift := bpz_shift_all hH P X M γ μ α₁ α₂ α₃ hγ hγ₂ hμ hαlo hαhi hα₂ hα₃ hs hX hM hdiag
  intro a b c z hz
  rw [neg_div, hdiag M γ α₁ hγ hγ₂ hM hαlo hαhi hα₂ hα₃ hs z hz]
  change gaussCoefficientRatio a b c * _ = _ at hshift
  linear_combination ‖gaussFPlus H a b c z‖ ^ 2 * hshift

end DOZZ.Proofs
