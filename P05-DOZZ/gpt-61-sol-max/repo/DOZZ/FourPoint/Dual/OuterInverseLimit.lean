/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.OuterInverseGuard
public import DOZZ.GMC.WeightedInverseLimit
public import DOZZ.FourPoint.NormalizedLimit
import Mathlib.Tactic

/-! # Dominated convergence of the actual dual outer inverse moments -/
public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Every inverse order converges, with a fixed exterior disk providing an integrable majorant. -/
abbrev dual_outerMass_inverse_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ ξ q : ℝ) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁ - 2 / γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :=
  gmc_inverse_moment_tendsto_of_disk_lower
    (l := nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) P X hX γ hγ hγ₂ M hM q
    ((2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) i|) *
      (4 : ℝ) ^ (-|γ * α₃|)) hq (by positivity)
    (fun z ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ)
    (fun ω => rho γ (M ω) (α₁ - 2 / γ) α₂ α₃)
    (Eventually.of_forall fun z =>
      (dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
        (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM))
    (by
      filter_upwards [eventually_punctured_zero_small] with z hz ω
      exact dual_outerMass_fixed_disk_lower γ α₁ α₂ α₃ ξ (M ω) z hz.2.2
        (by
          simpa only [Real.one_rpow] using Real.rpow_le_rpow (norm_nonneg z) hz.2.2
            (sub_nonneg.mpr hξ₁.le)))
    (dual_outerMass_ae_tendsto P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ hξ hξ₁ hα₁ hα₂ hα₃)

end DOZZ.Proofs
