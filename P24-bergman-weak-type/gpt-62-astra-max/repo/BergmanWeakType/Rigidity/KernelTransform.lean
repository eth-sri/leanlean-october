/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.AnalyticInverse
public import BergmanWeakType.Rigidity.ChangeOfVariables
public import BergmanWeakType.Measure
public import BergmanWeakType.Domain
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ComplexConjugate Topology

namespace BergmanWeakType

/-- Only reproduction at the *center* is needed on the disk: this is the
ordinary mean value theorem on every inner circle. -/
private theorem disk_mean {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g disk) (hi : Integrable g diskArea) :
    ∫ w, g w ∂diskArea = g 0 := by
  let := radialLaw_prob (α := 0) (by norm_num)
  rw [disk_polar hi, show g 0 = ∫ _, g 0 ∂radialLaw 0 by simp]
  apply integral_congr_ae
  filter_upwards [ae_radial 0] with r hr
  apply DiffContOnCl.circleAverage (hg.diffContOnCl_ball _)
  exact Metric.closedBall_subset_ball (by simpa [abs_of_pos hr.1] using hr.2)

/-- Both sections of a Hermitian Bergman kernel are square integrable. -/
theorem IsBergmanKernel.column_memLp {Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    (hK : IsBergmanKernel Ω K) (hΩ : MeasurableSet Ω) {z : ℂ} (hz : z ∈ Ω) :
    MemLp (fun w ↦ K w z) 2 (area.restrict Ω) := by
  refine (memLp_congr_ae ?_).mp (hK.squareIntegrable z hz).star
  filter_upwards [ae_restrict_mem hΩ] with w hw
  exact (hK.hermitian w hw z hz).symm

namespace Chart
open Function Complex
variable {U V : Set ℂ} {φ : ℂ → ℂ} (e : Chart U V φ) {K : ℂ → ℂ → ℂ}
include e

/-- Pullback as a holomorphic one-form preserves the Bergman space. -/
private theorem pull {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f V) (hi : MemLp f 2 (area.restrict V)) :
    DifferentiableOn ℂ (fun u ↦ deriv φ u * f (φ u)) U ∧
    MemLp (fun u ↦ deriv φ u * f (φ u)) 2 (area.restrict U) := by
  have c := (e.reg.diff.analyticOnNhd e.src).deriv.differentiableOn.mul (hd.comp e.reg.diff e.bij.mapsTo)
  refine ⟨c, (memLp_two_iff_integrable_sq_norm (c.continuousOn.aestronglyMeasurable e.src.measurableSet)).mpr ?_⟩
  have h := hi.integrable_norm_pow two_ne_zero
  rw [← e.bij.image_eq] at h
  simpa [IntegrableOn,mul_pow] using (area_integrableOn_image_iff_norm_deriv_sq e.src e.reg.diff e.bij.injOn _).mp h

omit e
variable {Ω : Set ℂ} (c : Chart disk Ω φ) (hK : IsBergmanKernel Ω K)
include c hK

/-- In the centered chart, reproduce the inverse derivative on the domain and
apply the disk mean value theorem to the conjugate, pulled-back column. -/
theorem center_row {w : ℂ} (hw : w ∈ disk) :
    deriv φ 0 * K (φ 0) (φ w) = conj ((deriv φ w)⁻¹) := by
  obtain ⟨hd,hi⟩ := c.symm.pull (by fun_prop) (show MemLp (fun _ ↦ 1) 2 diskArea from memLp_const _)
  simp at hd hi
  have h := hK.reproduces _ hd hi _ (c.bij.mapsTo hw)
  rw [c.inverse_deriv hw, ← c.bij.image_eq, area_integral_image_eq c.src c.reg.diff c.bij.injOn] at h
  obtain ⟨hd',hi'⟩ := c.pull (hK.holomorphic _ (c.bij.mapsTo hw)) (hK.column_memLp c.dst.measurableSet (c.bij.mapsTo hw))
  change MemLp _ 2 diskArea at hi'
  rw [← disk_mean hd' (hi'.integrable (by norm_num)), ← h, ← integral_conj]
  apply setIntegral_congr_fun c.src.measurableSet; intro u hu; dsimp only
  rw [c.inverse_deriv hu, real_smul, ← normSq_eq_norm_sq, ← mul_conj,
    hK.hermitian (φ w) (c.bij.mapsTo hw) (φ u) (c.bij.mapsTo hu)]
  simp [field, c.reg u hu]

omit hK in
theorem recentered {z : ℂ} (hz : z ∈ disk) : Chart disk Ω (φ ∘ diskSwap z) :=
  ⟨c.src,c.dst,c.bij.comp (diskSwap_bijOn hz),c.reg.comp (diskSwap_regular hz) (diskSwap_bijOn hz).mapsTo⟩

/-- Center a chart at an arbitrary output point by the involution `diskSwap`.
Its derivative supplies precisely the usual disk kernel. -/
theorem disk_jacobian_formula {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    (‖deriv φ w‖ ^ 2 : ℝ) • K (φ z) (φ w) = deriv φ w * kernel z w / deriv φ z := by
  let T := diskSwap z
  have hm := (diskSwap_bijOn hz).mapsTo
  have chart := c.recentered hz
  have h := chart.center_row hK (hm hw)
  have dc u (hu : u ∈ disk) := ((c.reg.hd _ (hm hu)).comp u ((diskSwap_regular hz).hd u hu)).deriv
  simp [dc 0 (by simp), dc _ (hm hw), T, diskSwap_swap hz hw, inv_deriv_swap hz hw] at h
  rw [(diskSwap_hasDerivAt hz (by simp)).deriv, (diskSwap_hasDerivAt hz hw).deriv] at h
  rw [real_smul, ← normSq_eq_norm_sq, ← mul_conj]
  simp  at h
  have hp := ofReal_ne_zero.mpr (diskFactor_pos hz).ne'
  simp [kernel]
  have hn := denominator_ne hz ((mem_disk_iff _).mp hw).le
  simp only [starRingEnd_apply] at *
  ; have := star_ne_zero.mpr (c.reg w hw); grind

end Chart
end BergmanWeakType
