/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalSecondKernel
public import DOZZ.FourPoint.Fusion.LocalRooting

/-! # Rooting the local mixed second derivative contribution -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The literal local `r₂` spatial integral equals its rooted reference-measure integral. -/
abbrev fusion_localR2_rooting {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hβ : γ ^ 2 / 2 < γ * α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (s : ℝ) (hs : s < 0)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :=
  fusion_local_rooting P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃
    s hs z hz hz4 (fun x => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ))
    ((Complex.measurable_ofReal.comp
    ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp
      (measurable_const.prodMk measurable_id))).div (Complex.measurable_ofReal.comp ((measurable_id.sub_const z).norm.pow_const 2)))
    (by
      let B := Metric.ball (0 : ℂ) (1 / 2)
      let f := fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ)
      have hβ2 : γ * α₁ < 2 := by have h := (lt_div_iff₀ hγ).mp hα₁; nlinarith
      have hfi1 := fusion_localSecondKernel_integrable γ α₁ α₂ α₃ (by positivity) hβ hβ2 z hz
      have heq : (fun x : ℂ => (‖B.indicator
          (fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2) x‖ : ℂ)) =
          B.indicator f := by
        funext x
        by_cases hx : x ∈ B
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, fusion_secondKernel_norm]
          simp only [f, Complex.ofReal_div]
        simp_all
      have hfi : Integrable (B.indicator f) gmcReferenceMeasure := heq ▸ hfi1.norm.ofReal
      exact hfi
    )

end DOZZ.Proofs
