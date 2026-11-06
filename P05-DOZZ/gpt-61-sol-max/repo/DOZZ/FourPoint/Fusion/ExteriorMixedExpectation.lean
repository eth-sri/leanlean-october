/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ExteriorMixedIntegral
public import DOZZ.FourPoint.Fusion.ExteriorExpectation
public import DOZZ.FourPoint.Fusion.MassPositiveFinite
public import DOZZ.FourPoint.TaylorFixedDisk

/-! # Uniform bounds on the signed exterior expectation -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The exterior rooted Taylor expectation is uniformly bounded by the preceding inverse moment. -/
abbrev fusion_exteriorR2_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (p : ℝ) (hp : 0 ≤ p) :=
  fusion_exterior_expectation_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
    (fun z x => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ))
    (fun z => (Complex.measurable_ofReal.comp
    ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp
      (measurable_const.prodMk measurable_id))).div (Complex.measurable_ofReal.comp ((measurable_id.sub_const z).norm.pow_const 2)))
    (by
      intro z hz hz4
      filter_upwards [fusion_gammaHalfMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ z hz hz4,
        gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
        gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
        gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hω hωz hω0 hω1
      simpa only [show -p - 1 + 1 = -p by ring] using
        fusion_exterior_mixed_inverse_integral_bound γ α₁ α₂ α₃ (-p - 1) z hz4 (M ω) hω.1 hω.2.lt_top hωz hω0 hω1
    )

end DOZZ.Proofs
