/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceOuterMoments
import Mathlib.Tactic
public import DOZZ.FourPoint.Fusion.RetainedRadialMoments
/-! Finite actual radial-weighted inverse moments and their signed real expectation interface. -/
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual radial-weighted inverse moment has an integrable real representative, and
its signed real expectation equals the ENNReal expectation converted to real. -/
theorem reflected_radial_scale_real_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (ν h s α₁ α₂ α₃ ξ q : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1) :
    Integrable (fun ω => (reflected_radial_scale γ ν h Xc z ω)^s*
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q)) P ∧
    (∫ ω, (reflected_radial_scale γ ν h Xc z ω)^s*
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q) ∂P) =
    (∫⁻ ω, ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)*
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P).toReal :=
  fusion_radial_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    (-γ / 2) (γ ^ 2 / 2) ν h s α₁ α₂ α₃ ξ q hh hξ hξ1 hq z hz0 hz

end DOZZ.Proofs
