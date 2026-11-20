/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RootedMass
import DOZZ.GMC.SharpMoments.SeibergMoment
public import DOZZ.FourPoint.Fusion.Kernel
import DOZZ.GMC.Construction.RootedMeasureKernel

/-! # Finiteness of the limiting rooted mass -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ)
  (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
include Ω X hX hγ hγ2 hM hα₁ hα₂ hα₃

/-- The limiting rooted mass in either fusion regime is almost surely finite. -/
theorem fusion_rootedMass_finite_ae :
    ∀ᵐ ω ∂P, gammaHalfRootedMass γ α₁ α₂ α₃ M ω < ⊤ := by
  have hz : Function.Injective (![0, 1] : Fin 2 → ℂ) :=
    Matrix.injective_pair_iff_ne.mpr zero_ne_one
  have ha : ∀ j : Fin 2, (![α₁ + γ / 2, α₂] : Fin 2 → ℝ) j < Q γ := by
    intro j
    fin_cases j
    · change α₁ + γ / 2 < Q γ
      unfold Q
      linarith
    · exact hα₂
  filter_upwards [fusion_gammaHalfRootedMass_eq_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃,
    coulombMass_ae_lt_top P X hX γ hγ hγ2 M hM ![0, 1] hz ![α₁ + γ / 2, α₂] α₃ ha hα₃] with ω he hf
  rw [he]
  exact hf

/-- The real limiting rooted kernel is integrable almost surely, as required by exterior DCT. -/
theorem fusion_limitingRootedKernel_finite_ae :
    ∀ᵐ ω ∂P, (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
      Real.exp (γ ^ 2 * gffKernel 0 x)) ∂M ω) < ⊤ := by
  have hd : Measurable (fun x : ℂ => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel 0 x))) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul (measurable_pointRootPotential.comp
        (measurable_const.prodMk measurable_id))).exp)
  have hk : Measurable (fun x : ℂ => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x)) :=
    ENNReal.measurable_ofReal.comp ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp
      (f := fun x : ℂ => ((0 : ℂ), x)) (measurable_const.prodMk measurable_id))
  filter_upwards [fusion_rootedMass_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hf h0 h1
  have hr0 : gmcRootedMeasure γ 0 (M ω) {0} = 0 := withDensity_absolutelyContinuous _ _ h0
  have hr1 : gmcRootedMeasure γ 0 (M ω) {1} = 0 := withDensity_absolutelyContinuous _ _ h1
  rw [gammaHalfRootedMass,
    fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ 0 _ hr0 hr0 hr1,
    gmcRootedMeasure, lintegral_withDensity_eq_lintegral_mul _ hd hk] at hf
  have he : (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
      Real.exp (γ ^ 2 * gffKernel 0 x)) ∂M ω) =
      ∫⁻ x, (ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel 0 x)) *
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x)) ∂M ω := by
    apply lintegral_congr
    intro x
    rw [mul_comm, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [he]
  exact hf

end

end DOZZ.Proofs
