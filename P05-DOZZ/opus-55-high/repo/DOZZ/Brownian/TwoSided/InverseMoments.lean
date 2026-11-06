/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.Moments
import DOZZ.ShiftEquations.Strip.UnitBlock

/-! Initial-block inverse bounds with a common radial constant for all subcritical charges. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs
section
variable {Ω : Type*}

theorem twosided_inverse_moment_uniform_from_lateral
    [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kν : Set ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : ℝ → Ω → Measure ℝ)
    (hData : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      IsTwoSidedConditionedBrownianProcess P (B ν) ν ∧
        IsLateralGMCOf P γ (Z γ) ∧ IndepFun (B ν) (Z γ) P)
    (p N : ℝ) (hp : p < 0) (hνN : ∀ ν ∈ Kν, ν ≤ N)
    (L : ℝ≥0∞) (hL : L < ⊤)
    (hUnit : ∀ γ ∈ Kγ, (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ p ∂P) ≤ L) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) (Z γ) ω) p ∂P) ≤ C := by
  let θ := (-p) * 2
  have hθ : 0 ≤ θ := by linarith
  obtain ⟨C, hC, hOsc⟩ := isNegativeConditionedBrownianLaw_unitIncrement_exp_le θ N hθ
  refine ⟨C * L, ENNReal.mul_lt_top hC hL, ?_⟩
  intro γ hγ ν hν
  obtain ⟨hB, hZ, hi⟩ := hData γ hγ ν hν
  let X : Ω → BrownianPath := fun ω => (B ν ω).1
  have hX : IsNegativeConditionedBrownianProcess P X ν := hB.1
  let f : BrownianPath → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianShiftPath 0 p)))
  let g : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Icc 0 1)) ^ p
  have hshift : Continuous (brownianShiftPath 0) :=
    continuous_brownianShiftPath.comp (continuous_const.prodMk continuous_id)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (continuous_brownianUnitNorm.comp hshift).measurable))
  have hg : Measurable g := ENNReal.continuous_rpow_const.measurable.comp
    (Measure.measurable_coe measurableSet_Icc)
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hf.comp_aemeasurable hX.1) (hg.comp_aemeasurable hZ.2.2.2.1) ((hi.comp measurable_fst measurable_id).comp hf hg)
  change _ =
    (∫⁻ ω, f (X ω) ∂P) * (∫⁻ ω, g _ ∂P) at hprod
  have hfX : (∫⁻ ω, f (X ω) ∂P) ≤ C := by
    rw [← lintegral_map' hf.aemeasurable hX.1]
    exact hOsc ν (hνN ν hν) _ hX.2 0
  have hUnit' : (∫⁻ ω, g (Z γ ω) ∂P) ≤ L := by
    rw [lateralGMC_Icc_moment_eq_Ioc P γ (Z γ) hZ 0 1 p (by norm_num)]
    exact hUnit γ hγ
  calc (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) (Z γ) ω) p ∂P)
      ≤ ∫⁻ ω, f (X ω) * g (Z γ ω) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [(ae_of_ae_map hX.1 hX.2.2.2.1), hZ.2.2.2.2.1] with ω h0 hfin
        have hlow := (initialUnitBlockMass_ge γ hZ.1.le (X ω) _).trans
          (DOZZ.Proofs.lastone_initialUnitBlockMass_le γ (B ν) (Z γ) ω)
        rw [h0, zero_sub] at hlow
        have h := ennreal_rpow_antitone_nonpos _ _ p hlow hp.le
        rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hfin 0 1).ne,
          ennreal_exp_rpow] at h
        have he : γ * -brownianUnitNorm (brownianShiftPath 0 (X ω)) * p =
            (-p) * γ * brownianUnitNorm (brownianShiftPath 0 (X ω)) := by ring
        rw [he] at h
        apply h.trans
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hZ.2.1.le (neg_nonneg.mpr hp.le)) (norm_nonneg _)
    _ = (∫⁻ ω, f (X ω) ∂P) * (∫⁻ ω, g _ ∂P) := hprod
    _ ≤ C * L := mul_le_mul' hfX hUnit'

end

end DOZZ.Proofs
