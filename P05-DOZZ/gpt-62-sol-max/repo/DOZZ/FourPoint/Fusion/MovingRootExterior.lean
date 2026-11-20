/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.Kernel
public import DOZZ.FourPoint.Fusion.RootedMass
public import DOZZ.FourPoint.Fusion.MovingRootFiniteness
import DOZZ.GMC.Construction.RootedMeasureKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import DOZZ.FourPoint.Fusion.MovingMass

/-! # Domination away from the colliding roots -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The rooting density as a product of distance powers away from the diagonal. -/
theorem fusion_rootDensity_formula (γ : ℝ) (u x : ℂ) (hxu : x ≠ u) :
    Real.exp (γ ^ 2 * gffKernel u x) =
      normPlus u ^ (γ ^ 2) * normPlus x ^ (γ ^ 2) * ‖x - u‖ ^ (-γ ^ 2) := by
  have hu : 0 < normPlus u := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hx : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd : 0 < ‖x - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxu)
  rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hd,
    ← Real.exp_add, ← Real.exp_add, gffKernel, norm_sub_rev]
  congr 1
  ring

/-- The distance powers are bounded by the fused zero-root power away from a collision. -/
theorem fusion_exterior_power_bound (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (hk : 0 ≤ k) (hca : c ≤ 2 * a) (hab : a / 2 ≤ b) :
    c ^ k * b ^ (-(2 * k)) ≤ (2 : ℝ) ^ (3 * k) * a ^ (-k) := by
  have hc' : c ^ k ≤ (2 * a) ^ k := Real.rpow_le_rpow hc hca hk
  have hb' : b ^ (-(2 * k)) ≤ (a / 2) ^ (-(2 * k)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hab (by linarith)
  calc
    _ ≤ (2 * a) ^ k * (a / 2) ^ (-(2 * k)) :=
      mul_le_mul hc' hb' (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le,
        Real.div_rpow ha.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      calc
        _ = ((2 : ℝ) ^ k * (2 : ℝ) ^ (2 * k)) * (a ^ k * a ^ (-(2 * k))) := by ring
        _ = (2 : ℝ) ^ (k + 2 * k) * a ^ (k + -(2 * k)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add ha]
        _ = _ := by congr 2 <;> ring

section
variable (γ α₁ α₂ α₃ : ℝ)

/-- Moving rooted kernels are dominated by the limiting kernel outside a fixed disk. -/
theorem fusion_rootedKernel_exterior_bound (z u x : ℂ)
    (hx : x ≠ 0) (hz : ‖z‖ ≤ ‖x‖) (hu : ‖u‖ ≤ ‖x‖ / 2) (hu1 : ‖u‖ ≤ 1) :
    gammaHalfKernel γ α₁ α₂ α₃ z x * Real.exp (γ ^ 2 * gffKernel u x) ≤
      (2 : ℝ) ^ (3 * (γ ^ 2 / 2)) *
        (gammaHalfKernel γ α₁ α₂ α₃ 0 x * Real.exp (γ ^ 2 * gffKernel 0 x)) := by
  have ha : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb : ‖x‖ / 2 ≤ ‖x - u‖ := by
    have h := norm_sub_norm_le x u
    linarith
  have hxu : x ≠ u := by
    intro he
    rw [he] at hu
    have hu0 : 0 < ‖u‖ := by simpa [he] using ha
    linarith
  have hc : ‖x - z‖ ≤ 2 * ‖x‖ := by
    have h := norm_sub_le x z
    linarith
  have hm := fusion_exterior_power_bound ‖x‖ ‖x - u‖ ‖x - z‖ (γ ^ 2 / 2)
    ha (norm_pos_iff.mpr (sub_ne_zero.mpr hxu)) (norm_nonneg _) (by positivity) hc hb
  have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hpx : normPlus u = 1 := max_eq_left hu1
  rw [fusion_rootDensity_formula γ u x hxu, hpx, Real.one_rpow, one_mul,
    fusion_rootDensity_formula γ 0 x hx]
  simp only [normPlus, norm_zero, max_eq_left zero_le_one, Real.one_rpow, one_mul,
    gammaHalfKernel, sub_zero]
  have hpow : ‖x‖ ^ (γ ^ 2 / 2) * ‖x‖ ^ (-γ ^ 2) = ‖x‖ ^ (-(γ ^ 2 / 2)) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have he : -(2 * (γ ^ 2 / 2)) = -γ ^ 2 := by ring
  rw [he] at hm
  have hf : 0 ≤ normPlus x ^ (γ * (α₁ + α₂ + α₃ - γ / 2)) * normPlus x ^ (γ ^ 2) /
      (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂)) := by positivity
  have h := mul_le_mul_of_nonneg_right hm hf
  have heq : ‖x‖ ^ (-(γ ^ 2 / 2)) = ‖x‖ ^ (γ ^ 2 / 2) * ‖x‖ ^ (-γ ^ 2) := hpow.symm
  rw [heq] at h
  unfold normPlus at h
  convert h using 1 <;> ring

theorem fusionRootedKernel_exterior_le (w u x : ℂ)
    (hx : x ≠ 0) (hw : ‖w‖ ≤ ‖x‖) (hu : ‖u‖ ≤ ‖x‖ / 2) (hu1 : ‖u‖ ≤ 1) :
    fusionRootedKernel γ α₁ α₂ α₃ w u x ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * (γ ^ 2 / 2))) * fusionRootedKernel γ α₁ α₂ α₃ 0 0 x := by
  have h := ENNReal.ofReal_le_ofReal (fusion_rootedKernel_exterior_bound γ α₁ α₂ α₃ w u x hx hw hu hu1)
  rwa [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at h

/-- Dominated convergence outside a fixed disk, with two independently moving insertions. -/
theorem fusion_rootedKernel_exterior_tendsto (μ : Measure ℂ)
    (δ : ℝ) (hδ : 0 < δ) {w u : ℂ → ℂ}
    (hw : Tendsto w (nhds 0) (nhds 0)) (hu : Tendsto u (nhds 0) (nhds 0))
    (hfin : fusionRootedMass γ α₁ α₂ α₃ 0 0 μ < ⊤) :
    Tendsto (fun z => fusionRootedGoodMass γ α₁ α₂ α₃ (w z) (u z) δ μ) (nhds 0)
      (nhds (fusionRootedGoodMass γ α₁ α₂ α₃ 0 0 δ μ)) := by
  let F := fusionRootedKernel γ α₁ α₂ α₃
  let C : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (3 * (γ ^ 2 / 2)))
  have hwlim : Tendsto (fun z => ‖w z‖) (nhds 0) (nhds 0) := by simpa only [norm_zero] using hw.norm
  have hulim : Tendsto (fun z => ‖u z‖) (nhds 0) (nhds 0) := by simpa only [norm_zero] using hu.norm
  apply tendsto_lintegral_filter_of_dominated_convergence (fun x => C * F 0 0 x)
  · exact Eventually.of_forall fun z => fusionRootedKernel_measurable γ α₁ α₂ α₃ (w z) (u z)
  · filter_upwards [hwlim.eventually_lt_const hδ, hulim.eventually_lt_const (half_pos hδ),
      hulim.eventually_lt_const zero_lt_one] with z hz huδ hu1
    filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm)] with x hx
    exact fusionRootedKernel_exterior_le γ α₁ α₂ α₃ (w z) (u z) x
      (norm_ne_zero_iff.mp (hδ.trans_le hx).ne') (hz.le.trans hx) (by linarith) hu1.le
  · rw [lintegral_const_mul _ (fusionRootedKernel_measurable γ α₁ α₂ α₃ 0 0)]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hfin)).ne
  · filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm)] with x hx
    exact fusion_rootedKernel_tendsto γ α₁ α₂ α₃ x (norm_ne_zero_iff.mp (hδ.trans_le hx).ne') hw hu

end

end DOZZ.Proofs
