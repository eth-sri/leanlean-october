/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MeasurableIntegralFamily
public import DOZZ.FourPoint.Fusion.MovingMass
import Mathlib.MeasureTheory.Integral.Prod
import DOZZ.GMC.Annulus.BallCover
import DOZZ.GMC.SharpMoments.SeibergPieces
public import DOZZ.GMC.SharpMoments.SeibergWeight
public import DOZZ.GMC.Construction.GMCMeasurableVersion

/-! # Jointly measurable unrooted spatial expectations -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem measurable_gammaHalf_coulombMass (γ α₁ α₂ α₃ : ℝ) :
    Measurable (fun q : ℂ × FiniteMeasure ℂ =>
      coulombMass γ q.2.toMeasure ![-γ / 2, α₁, α₂] ![q.1, 0, 1] α₃) := by
  refine measurable_coulombMass_family γ ![-γ / 2, α₁, α₂] (fun u : ℂ => ![u, 0, 1]) (fun j => ?_) α₃
  fin_cases j
  · exact measurable_id
  · exact measurable_const
  · exact measurable_const

/-- The literal signed spatial expectation is measurable in the moving point. -/
theorem fusion_gammaHalf_spatial_expectation_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (H : ℂ × ℂ → ℂ) (hH : Measurable H) :
    Measurable (fun z : ℂ => ∫ ω,
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s).toReal : ℂ) *
        (∫ x, H (z, x) ∂M ω) ∂P) := by
  letI := hX.1
  exact measurable_integral_ae_parameter (equatorGFF_finiteGMC_aemeasurable P X hX γ hγ hγ2 M hM)
    ((Complex.measurable_ofReal.comp ((measurable_gammaHalf_coulombMass γ α₁ α₂ α₃).pow_const s).ennreal_toReal).mul
      (measurable_integral_finiteMeasure_parameter hH))

end DOZZ.Proofs
