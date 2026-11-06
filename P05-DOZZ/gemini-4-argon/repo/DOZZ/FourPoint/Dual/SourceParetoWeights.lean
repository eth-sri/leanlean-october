/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceRadialMoments
public import DOZZ.FourPoint.Reflected.ParetoProductIncrement
import Mathlib.Tactic
/-! The actual source parameters supply both moment inputs of the signed Pareto estimate. -/
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- The source retained mass and actual restart scale supply both integrable Pareto weights;
positive finite mass is proved from source moments rather than assumed. -/
theorem dual_source_pareto_weights_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hc : IsCircleAverage P X Xc)
    (ν h p α₁ α₂ α₃ ξ : ℝ) (hν : 0 < ν) (hh : 0 ≤ h) (hp : 0 < p)
    (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    z (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1) :
    let A := fun ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
    let b := dual_radial_scale γ ν h Xc z
    (∀ᵐ ω ∂P, 0 < A ω) ∧
      Integrable (fun ω => (A ω)^(-p)*(b ω/A ω)^(2*ν/γ)) P ∧
      Integrable (fun ω => (A ω)^(-p)*(b ω/A ω)) P := by
  let A := fun ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := dual_radial_scale γ ν h Xc z
  let a := 2*ν/γ
  have hpos : ∀ᵐ ω ∂P, 0 < A ω :=
    (dual_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hz (by simpa only [Real.one_rpow] using Real.rpow_le_rpow (norm_nonneg z) hz (sub_nonneg.mpr hξ1.le))).mono
        fun ω hω => ENNReal.toReal_pos hω.1.ne' hω.2.ne
  have hβ (ω : Ω) : 0 ≤ b ω := by
    dsimp only [b,dual_radial_scale]
    exact (Real.exp_pos _).le
  have h0 := (dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    ν h a α₁ α₂ α₃ ξ (p+a) hh hξ hξ1 (add_pos hp (div_pos (mul_pos (by norm_num) hν) hγ)).le z hz0 hz).1
  have h1 := (dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    ν h 1 α₁ α₂ α₃ ξ (p+1) hh hξ hξ1 (by linarith only [hp]) z hz0 hz).1
  simp only [(show -(p+a) = -p-a by ring)] at h0
  simp only [(show -(p+1) = -p-1 by ring),Real.rpow_one] at h1
  refine ⟨hpos, h0.congr ?_, h1.congr ?_⟩
  · filter_upwards [hpos] with ω hω
    exact (reflected_pareto_parameter_weights p a (A ω) (b ω) hω (hβ ω)).1.symm
  · filter_upwards [hpos] with ω hω
    exact (reflected_pareto_parameter_weights p a (A ω) (b ω) hω (hβ ω)).2.symm

end DOZZ.Proofs
