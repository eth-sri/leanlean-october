/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.MaximumMoment
public import DOZZ.ShiftEquations.Strip.UnitBlock
public import DOZZ.Correlations.Tails.WilliamsPolarMassLaw

/-! Expectation bounds on the independent Williams maximum/conditioned-path model. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs


/-- On the Williams model, the critical moment is between twice the initial-block moment
and twice the full reflection-mass moment. The cutoff may depend on the maximum. -/
theorem lastone_williamsModel_moment_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hBm : AEMeasurable B P) (hZm : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Icc a b) < ⊤) :
    2 * (∫⁻ ω, initialUnitBlockMass γ (B ω).1 (Z ω) ^ (ν / γ) ∂P) ≤
      (∫⁻ z : ℝ × Ω,
        williamsMassFunctional γ
          (((z.1, negativeConditionedLastExitSegment z.1 (B z.2).2), (B z.2).1), Z z.2)
            ^ (ν / γ) ∂(brownianMaximumReferenceLaw ν).prod P) ∧
      (∫⁻ z : ℝ × Ω,
        williamsMassFunctional γ
          (((z.1, negativeConditionedLastExitSegment z.1 (B z.2).2), (B z.2).1), Z z.2)
            ^ (ν / γ) ∂(brownianMaximumReferenceLaw ν).prod P) ≤
        2 * (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^ (ν / γ) ∂P) := by
  have lastone_height_product_moment (f : Ω → ℝ≥0∞) (hf : AEMeasurable f P) : (∫⁻ z : ℝ × Ω, (ENNReal.ofReal (Real.exp (γ * z.1)) * f z.2) ^ (ν / γ) ∂(brownianMaximumReferenceLaw ν).prod P) = 2 * ∫⁻ ω, f ω ^ (ν / γ) ∂P := by
    let : IsProbabilityMeasure (brownianMaximumReferenceLaw ν) :=
      isProbabilityMeasure_brownianMaximumReferenceLaw hν
    calc
      _ = ∫⁻ z : ℝ × Ω,
          ENNReal.ofReal (Real.exp (ν * z.1)) * f z.2 ^ (ν / γ)
            ∂(brownianMaximumReferenceLaw ν).prod P := lintegral_congr fun z => (fun (m : ℝ) (ω : Ω) => by rw [ENNReal.mul_rpow_of_nonneg _ _ (div_pos hν hγ).le, ennreal_exp_rpow]; congr 2; field_simp) z.1 z.2
      _ = (∫⁻ m, ENNReal.ofReal (Real.exp (ν * m)) ∂brownianMaximumReferenceLaw ν) *
          ∫⁻ ω, f ω ^ (ν / γ) ∂P := lintegral_prod_mul ((by fun_prop : Measurable (fun m => ENNReal.ofReal (Real.exp (ν * m)))).aemeasurable)
            (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf)
      _ = _ := by rw [lastone_maximum_exp_moment ν hν]
  let : IsProbabilityMeasure (brownianMaximumReferenceLaw ν) :=
    isProbabilityMeasure_brownianMaximumReferenceLaw hν
  have hpair := hBm.prodMk hZm
  have hIm : AEMeasurable (twoSidedReflectionMass γ B Z) P :=
    (aemeasurable_reflectionMassInput_map_of_locallyFinite P γ
      (fun ω => (B ω, Z ω)) hpair (by filter_upwards [hfin] with ω hω n; exact hω (-(n : ℝ)) (n : ℝ))).comp_aemeasurable hpair
  have heq : ∀ᵐ z : ℝ × Ω ∂(brownianMaximumReferenceLaw ν).prod P,
      williamsMassFunctional γ
        (((z.1, negativeConditionedLastExitSegment z.1 (B z.2).2), (B z.2).1), Z z.2) =
        ENNReal.ofReal (Real.exp (γ * z.1)) * twoSidedReflectionCutMass γ z.1 B Z z.2 := by
    filter_upwards [((measurePreserving_snd (μ := brownianMaximumReferenceLaw ν) (ν := P)).quasiMeasurePreserving).ae hfin] with z hz
    exact williamsMassFunctional_lastExit γ z.1 (B z.2).1 (B z.2).2 (Z z.2) hz
  constructor
  · rw [← lastone_height_product_moment _ (initialUnitBlockMass_aemeasurable P γ (fun ω => (B ω).1) Z hBm.fst hZm hfin)]
    apply lintegral_mono_ae
    filter_upwards [heq] with z hz
    rw [hz]
    exact ENNReal.rpow_le_rpow
      (mul_le_mul' le_rfl (initialUnitBlockMass_le_cutMass γ z.1 B Z z.2)) (div_pos hν hγ).le
  · rw [← lastone_height_product_moment _ hIm]
    apply lintegral_mono_ae
    filter_upwards [heq] with z hz
    rw [hz]
    exact ENNReal.rpow_le_rpow
      (mul_le_mul' le_rfl (twoSidedReflectionCutMass_le_mass γ z.1 B Z z.2)) (div_pos hν hγ).le

end DOZZ.Proofs
