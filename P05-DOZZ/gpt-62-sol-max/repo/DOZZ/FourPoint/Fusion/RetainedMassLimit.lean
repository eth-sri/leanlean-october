/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RetainedInverseMass
public import DOZZ.FourPoint.BPZ.Weight
import DOZZ.FourPoint.Reflected.MassFiniteness
import DOZZ.GMC.Construction.RootedCircleMassLimit
import Mathlib.Tactic

/-! The moving exterior cutoff can be removed after merging the moving charge `-χ`
into the charge at zero. This argument works for both degenerate insertions. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- On the retained set the moving root is absent. -/
theorem fusionOuterMass_eq_lintegral (γ χ α₁ α₂ α₃ ξ : ℝ) (z : ℂ) (μ : Measure ℂ)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) (hz : ‖z‖ < ‖z‖ ^ (1 - ξ)) :
    fusionOuterMass γ (-χ) α₁ α₂ α₃ μ z ξ =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖},
        ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x) ∂μ := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hnull (x : ℂ) (hx : μ {x} = 0) : (μ.restrict D) {x} = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.restrict_le_self (s := D)) {x} |>.trans_eq hx)
  have hz' : (μ.restrict D) {z} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton z),
      singleton_inter_of_notMem (show z ∉ D from not_le.mpr hz), measure_empty]
  exact coulombMass_eq_lintegral_bpzSoftWeight (μ.restrict D) z hz' (hnull 0 h0) (hnull 1 h1)

/-- At zero the two charges combine, away from the fused root. -/
theorem fusion_zero_kernel_weight (γ χ α₁ α₂ α₃ : ℝ) (x : ℂ) (hx : x ≠ 0) :
    bpzSoftWeight γ χ α₁ α₂ α₃ 0 0 x =
      normPlus x ^ (γ * ((α₁ - χ) + α₂ + α₃)) /
        (‖x‖ ^ (γ * (α₁ - χ)) * ‖x - 1‖ ^ (γ * α₂)) := by
  rw [bpzSoftWeight_zero, bpzBaseWeight, sub_zero, ← mul_assoc, ← mul_assoc,
    ← Real.rpow_add (norm_pos_iff.mpr hx), show γ * χ + -(γ * α₁) = -(γ * (α₁ - χ)) by ring,
    show α₁ + α₂ + α₃ - χ = α₁ - χ + α₂ + α₃ by ring,
    Real.rpow_neg (norm_nonneg _), Real.rpow_neg (norm_nonneg _), div_eq_mul_inv, mul_inv]
  ring

/-- Dominated removal of the cutoff, using the fused kernel as a majorant. -/
theorem fusionOuterMass_tendsto (γ χ α₁ α₂ α₃ ξ : ℝ) (μ : Measure ℂ)
    (hγχ : 0 ≤ γ * χ) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hfin : rho γ μ (α₁ - χ) α₂ α₃ ≠ ⊤) :
    Tendsto (fun z : ℂ => fusionOuterMass γ (-χ) α₁ α₂ α₃ μ z ξ)
      (𝓝[≠] (0 : ℂ)) (𝓝 (rho γ μ (α₁ - χ) α₂ α₃)) := by
  let l := 𝓝[≠] (0 : ℂ)
  let K := bpzSoftWeight γ χ α₁ α₂ α₃ 0
  let D (z : ℂ) : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  let F (z : ℂ) := (D z).indicator (fun x => ENNReal.ofReal (K z x))
  let C := ENNReal.ofReal ((2 : ℝ) ^ (γ * χ))
  let G (x : ℂ) := C * ENNReal.ofReal (K 0 x)
  have hD z : MeasurableSet (D z) := (isClosed_le continuous_const continuous_norm).measurableSet
  have hn : Tendsto (fun z : ℂ => ‖z‖) l (𝓝 0) :=
    (tendsto_norm_zero (E := ℂ)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ z in l, ‖z‖ < ‖z‖ ^ (1 - ξ) := by
    filter_upwards [hn.eventually_lt_const zero_lt_one, self_mem_nhdsWithin] with z hz hz0
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt
      (norm_pos_iff.mpr hz0) hz (show 1 - ξ < 1 by linarith)
  have h0ae : ∀ᵐ x ∂μ, x ≠ 0 := measure_eq_zero_iff_ae_notMem.mp h0
  have hmerge : (∫⁻ x, ENNReal.ofReal (K 0 x) ∂μ) = rho γ μ (α₁ - χ) α₂ α₃ :=
    lintegral_congr_ae (h0ae.mono fun x hx => congrArg ENNReal.ofReal
      (fusion_zero_kernel_weight γ χ α₁ α₂ α₃ x hx))
  have hfinite : (∫⁻ x, G x ∂μ) ≠ ⊤ := by
    dsimp only [G]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmerge]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hbound : ∀ᶠ z in l, ∀ᵐ x ∂μ, F z x ≤ G x := hsmall.mono fun z hz =>
    Eventually.of_forall fun x => by
      by_cases hx : x ∈ D z
      · dsimp only [F, G, C, K]
        rw [indicator_of_mem hx, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
        apply ENNReal.ofReal_le_ofReal
        rw [bpzSoftWeight_zero, bpzSoftWeight_zero, sub_zero, ← mul_assoc,
          ← Real.mul_rpow (by norm_num) (norm_nonneg x), two_mul]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (norm_nonneg _) ((norm_sub_le _ _).trans
            (add_le_add_right (hz.le.trans hx) _)) hγχ) (bpzBaseWeight_nonneg x)
      · exact (indicator_of_notMem hx _).trans_le bot_le
  have hradius : Tendsto (fun z : ℂ => ‖z‖ ^ (1 - ξ)) l (𝓝 0) := by
    have he := sub_pos.mpr hξ₁
    simpa only [Function.comp_def, Real.zero_rpow he.ne'] using
      ((Real.continuous_rpow_const he.le).tendsto (0 : ℝ)).comp hn
  have hlimit : ∀ᵐ x ∂μ, Tendsto (fun z => F z x) l (𝓝 (ENNReal.ofReal (K 0 x))) :=
    h0ae.mono fun x hx => by
      have hc : Continuous (fun z : ℂ => K z x) := by
        simp only [K, bpzSoftWeight_zero]
        exact ((Real.continuous_rpow_const hγχ).comp
          (continuous_const.sub continuous_id).norm).mul_const _
      refine ((ENNReal.continuous_ofReal.comp hc).tendsto 0 |>.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hradius.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))] with z hz
      change ENNReal.ofReal (K z x) = (D z).indicator (fun y => ENNReal.ofReal (K z y)) x
      rw [indicator_of_mem (show x ∈ D z from hz.le)]
  have ht := tendsto_lintegral_filter_of_dominated_convergence G
    (Eventually.of_forall fun z => ((measurable_bpzSoftWeight 0 z).ennreal_ofReal).indicator (hD z))
    hbound hfinite hlimit
  rw [hmerge] at ht
  refine ht.congr' (hsmall.mono fun z hz => ?_)
  exact (lintegral_indicator (hD z) _).trans (fusionOuterMass_eq_lintegral γ χ α₁ α₂ α₃ ξ z μ h0 h1 hz).symm

/-- Inverse moments converge on the subcritical domain of the fused charges. -/
theorem fusionOuterMass_inverse_moment_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (χ α₁ α₂ α₃ ξ q : ℝ) (hγχ : 0 ≤ γ * χ) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁ - χ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ => ∫⁻ ω, fusionOuterMass γ (-χ) α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P)
      (𝓝[≠] (0 : ℂ)) (𝓝 (∫⁻ ω, rho γ (M ω) (α₁ - χ) α₂ α₃ ^ (-q) ∂P)) := by
  apply fusionOuterMass_inverse_moment_tendsto P X hX γ hγ hγ₂ M hM (-χ) α₁ α₂ α₃ ξ q hξ₁.le hq
  filter_upwards [gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ₂ M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ₂ M hM 1,
    reflected_rho_ae_finite P X hX γ hγ hγ₂ M hM (α₁ - χ) α₂ α₃ hα₁ hα₂ hα₃] with ω h0 h1 hf
  exact fusionOuterMass_tendsto γ χ α₁ α₂ α₃ ξ (M ω) hγχ hξ hξ₁ h0 h1 hf.ne

end DOZZ.Proofs
