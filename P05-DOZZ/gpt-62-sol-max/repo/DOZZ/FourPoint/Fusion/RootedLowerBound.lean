/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RootedMass
import DOZZ.GMC.Construction.RootedMeasureKernel
import DOZZ.GMC.SharpMoments.SeibergDecomp
public import DOZZ.GMC.SharpMoments.LocationTransfer
import DOZZ.GMC.SharpMoments.ArbitraryCenter
import DOZZ.GMC.SharpMoments.SeibergMoment
public import DOZZ.FourPoint.TaylorFixedDisk

/-! # A uniform lower bound for the rooted density

The covariance kernel is bounded below globally. Thus rooting preserves every fixed-disk
lower bound for the mass, uniformly in the location of the root.
-/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The equator covariance is bounded below even with the totalized diagonal value. -/
theorem fusion_gffKernel_lower (u x : ℂ) : -Real.log 2 ≤ gffKernel u x := by
  have hu : 1 ≤ normPlus u := le_max_left _ _
  have hx : 1 ≤ normPlus x := le_max_left _ _
  have hu0 : 0 < normPlus u := lt_of_lt_of_le zero_lt_one hu
  have hx0 : 0 < normPlus x := lt_of_lt_of_le zero_lt_one hx
  have hud : ‖u‖ ≤ normPlus u := le_max_right _ _
  have hxd : ‖x‖ ≤ normPlus x := le_max_right _ _
  have hb : ‖u - x‖ ≤ 2 * (normPlus u * normPlus x) := by
    have h1 : normPlus u ≤ normPlus u * normPlus x := le_mul_of_one_le_right hu0.le hx
    have h2 : normPlus x ≤ normPlus u * normPlus x := le_mul_of_one_le_left hx0.le hu
    have hn := norm_sub_le u x
    linarith
  by_cases hdiag : u = x
  · subst x
    simp only [gffKernel, sub_self, norm_zero, Real.log_zero, neg_zero, zero_add]
    have hlog := Real.log_nonneg hu
    have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · have hd : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hdiag)
    have hlog := Real.log_le_log hd hb
    rw [Real.log_mul (by norm_num) (mul_pos hu0 hx0).ne',
      Real.log_mul hu0.ne' hx0.ne'] at hlog
    unfold gffKernel
    linarith

/-- A positive constant bounds every rooted density from below. -/
theorem fusion_rootDensity_lower (γ : ℝ) (u x : ℂ) :
    ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (fusion_gffKernel_lower u x) (sq_nonneg γ)
  nlinarith only [h]

section
variable {N : ℕ} (γ : ℝ) (u : ℂ) (μ : Measure ℂ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ)
include N

/-- Rooting uniformly preserves a lower bound for any Coulomb mass. -/
theorem fusion_rootedCoulombMass_lower :
    ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) * coulombMass γ μ α z αinf ≤
      coulombMass γ (gmcRootedMeasure γ u μ) α z αinf := by
  have hd : Measurable (fun x : ℂ =>
      ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x))) := by
    exact ENNReal.measurable_ofReal.comp
      ((measurable_const.mul (measurable_pointRootPotential.comp
        (measurable_const.prodMk measurable_id))).exp)
  rw [coulombMass_eq_lintegral_coulombWeight, coulombMass_eq_lintegral_coulombWeight,
    gmcRootedMeasure, lintegral_withDensity_eq_lintegral_mul μ hd
      (measurable_coulombWeight _ _ _ _),
    ← lintegral_const_mul _ (measurable_coulombWeight _ _ _ _)]
  exact lintegral_mono fun x => mul_le_mul' (fusion_rootDensity_lower γ u x) le_rfl

/-- A retained region inherits the fixed-disk lower bound after rooting anywhere. -/
theorem rooted_coulombMass_fixed_disk_lower_restrict (hz : ∀ j, ‖z j‖ ≤ 1)
    {D : Set ℂ} (hD : MeasurableSet D) (hsub : Metric.ball (3 : ℂ) (1 / 8) ⊆ D) :
    ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2) * coulombGuardWeight γ α αinf) *
      μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
        coulombMass γ ((gmcRootedMeasure γ u μ).restrict D) α z αinf := by
  have he : (gmcRootedMeasure γ u μ).restrict D = gmcRootedMeasure γ u (μ.restrict D) :=
    restrict_withDensity hD _
  rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
  exact (mul_le_mul' le_rfl (coulombMass_fixed_disk_lower_restrict γ μ α z αinf hz hsub)).trans
    (fusion_rootedCoulombMass_lower γ u (μ.restrict D) α z αinf)

end

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {N : ℕ} (α : Fin N → ℝ)
include Ω X hX hγ hγ2 hM

/-- The same inverse moment constant works for all bounded insertions and every rooting point. -/
theorem rooted_coulomb_inverse_uniform (αinf q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℂ) (z : Fin N → ℂ), (∀ j, ‖z j‖ ≤ 1) →
      (∫⁻ ω, coulombMass γ (gmcRootedMeasure γ u (M ω)) α z αinf ^ (-q) ∂P) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC, h⟩ := inverse_fixed_disk_uniform P X hX γ hγ hγ2 M hM _ q
    (mul_pos (Real.exp_pos (-γ ^ 2 * Real.log 2)) (coulombGuardWeight_pos γ α αinf)) hq
  refine ⟨C, hC, fun u z hz => h _ fun ω => ?_⟩
  simpa only [Measure.restrict_univ] using rooted_coulombMass_fixed_disk_lower_restrict
    γ u (M ω) α z αinf hz MeasurableSet.univ (Set.subset_univ _)

/-- The fixed-disk domination gives a uniform finite inverse moment for all rooting points. -/
theorem fusion_rootedMass_inverse_moment_uniform (αinf s : ℝ) (hs : s ≤ 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (u : ℂ) (z : Fin N → ℂ), (∀ j, ‖z j‖ ≤ 1) →
      (∫⁻ ω, ENNReal.rpow (coulombMass γ (gmcRootedMeasure γ u (M ω)) α z αinf) s ∂P) ≤ C := by
  obtain ⟨C, _, h⟩ := rooted_coulomb_inverse_uniform P X hX γ hγ hγ2 M hM α αinf (-s) (neg_nonneg.mpr hs)
  exact ⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, by simpa only [neg_neg, ENNReal.rpow_eq_pow] using h⟩

end

end DOZZ.Proofs
