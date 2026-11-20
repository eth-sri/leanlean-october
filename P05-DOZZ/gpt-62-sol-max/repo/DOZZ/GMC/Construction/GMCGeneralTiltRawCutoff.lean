/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCGeneralTilt
public import DOZZ.GMC.Construction.GMCGeneralTiltScalarLimit
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure

/-! Raw-field measurable circle cutoffs and scalar versions of their GMC limits. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
include mΩ hX

/-- Raw-joint measurability of a circle field makes each cutoff measure raw measurable. -/
theorem regularizedGMC_raw_measurable_of_joint
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (hRaw : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
      (fun p : Ω × ℂ => Xc p.1 p.2 r)) :
    Measurable[equatorGFFRawDistributionSigma X]
      (fun ω => regularizedGMC P Xc γ r ω) := by
  letI := hX.1
  exact regularizedGMC_measurable_of_joint (mΩ := mΩ) (equatorGFFRawDistributionSigma X) P Xc γ r (hXc.1 r) hRaw

/-- Every bounded-continuous test integral of an `IsGMCOf` limit has a raw-measurable proxy. -/
theorem equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : BoundedContinuousFunction ℂ ℝ) :
    ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => ∫ x, f x ∂M ω) =ᵐ[P] g := by
  rcases hM with ⟨_, XcOld, hXcOld, hconvOld⟩
  obtain ⟨Xc, hXc, hRaw⟩ := exists_raw_equatorGFF_circle_average_witness X hX
  have hconv : ∀ f : BoundedContinuousFunction ℂ ℝ,
      TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂M ω) := by
    intro f
    have hEq (r : ℝ) :
        (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) =ᵐ[P]
          fun ω => ∫ x, f x ∂regularizedGMC P XcOld γ r ω := by
      filter_upwards [regularizedGMC_ae_eq_of_circleAverage P X hX
        Xc XcOld hXc hXcOld γ r] with ω hω
      rw [hω]
    exact TendstoInMeasure.congr (fun r => (hEq r).symm)
      (Filter.Eventually.of_forall fun _ => rfl) (hconvOld f)
  have hCut (r : ℝ) := regularizedGMC_raw_measurable_of_joint P X hX Xc hXc γ r (hRaw r)
  exact equatorGFF_GMC_testIntegral_raw_measurable_version
    P X γ Xc M hconv hCut f

end

end DOZZ.Proofs
