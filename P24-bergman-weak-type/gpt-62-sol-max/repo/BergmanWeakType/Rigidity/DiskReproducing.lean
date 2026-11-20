/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Domain
public import BergmanWeakType.Weighted.MassCoordinate
public import BergmanWeakType.Rigidity.ChangeOfVariables
public import BergmanWeakType.Rigidity.DiskShift
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public section

open Set Filter Metric MeasureTheory Complex Real
open scoped ComplexConjugate

namespace BergmanWeakType

/-- The disk area mean of an integrable holomorphic function is its value at zero. -/
private theorem integral_disk_eq_at_zero {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    (hfi : Integrable f diskArea) : (∫ w, f w ∂diskArea) = f 0 := by
  rw [integral_diskArea_eq_circleAverage_sqrt_one_sub hfi]
  calc
    _ = ∫ _y in (0 : ℝ)..1, f 0 := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro y hy
      apply DiffContOnCl.circleAverage
      apply (hf.mono (closure_ball_subset_closedBall.trans _)).diffContOnCl
      rw [abs_of_nonneg (sqrt_nonneg _)]
      exact fun w hw ↦ hw.trans_lt ((sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by linarith [hy.1]))
    _ = f 0 := by simp

private theorem memLp_kernel_top {z : ℂ} (hz : z ∈ disk) : MemLp (kernel z) ⊤ diskArea := by
  simpa only [weightedArea_zero, funext (weightedKernel_zero z)] using memLp_weightedKernel_top (α := 0) hz

/-- Reproduction at any point follows by shifting the disk and applying the area mean at zero. -/
theorem integral_kernel_mul_eq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    (hfi : Integrable f diskArea) {z : ℂ} (hz : z ∈ disk) :
    (∫ w, kernel z w * f w ∂diskArea) = f z := by
  let g := diskShift z
  let τ := 1 - z * conj z
  have hbij := diskShift_bijOn hz
  have hg := differentiableOn_diskShift hz
  have hd {w : ℂ} (hw : w ∈ disk) : deriv g w = τ / (1 + w * conj z) ^ 2 :=
    (hasDerivAt_diskShift hz hw).deriv
  have ht : τ ≠ 0 := diskShift_tau_ne_zero hz
  let F := fun w ↦ deriv g w * f (g w) / τ
  have heq (w : ℂ) (hw : w ∈ disk) :
      (‖deriv g w‖ ^ 2 : ℝ) • (kernel z (g w) * f (g w)) = F w := by
    have hn := diskShift_den_ne_zero hz hw
    have hh : (1 + conj w * z) ≠ 0 := by simpa using star_ne_zero.mpr hn
    have hK : 1 - z * conj (g w) = τ / (1 + conj w * z) := by
      simp [g, diskShift, τ]
      grind
    rw [Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [F, kernel, ← starRingEnd_apply, hK, hd hw, map_div₀, map_pow, map_add, map_mul, map_one,
      Complex.conj_conj, show conj τ = τ by simp [τ, mul_comm]]
    field_simp
  have hI := (area_integrableOn_image_iff_norm_deriv_sq (U := disk) isOpen_ball hg hbij.injOn
    (fun w ↦ kernel z w * f w)).mp (by
      rw [hbij.image_eq]
      exact hfi.mul_of_top_right (memLp_kernel_top hz))
  change (∫ w in disk, kernel z w * f w ∂area) = _
  rw [← hbij.image_eq, area_integral_image_eq (U := disk) isOpen_ball hg hbij.injOn]
  have he := ae_mem_disk.mono heq
  refine (integral_congr_ae he).trans ((integral_disk_eq_at_zero
    (((hg.analyticOnNhd isOpen_ball).deriv.differentiableOn.mul (hf.comp hg hbij.mapsTo)).div_const τ) (hI.congr he)).trans ?_)
  simp [hd (show (0 : ℂ) ∈ disk by simp), g, ht, mul_div_cancel_left₀]

/-- The explicit unit-disk kernel satisfies the standard Bergman-kernel characterization. -/
theorem isBergmanKernel_disk : IsBergmanKernel disk kernel where
  holomorphic w hw := by
    unfold kernel
    exact (((differentiableOn_const 1).sub
      (differentiableOn_id.mul_const (star w))).inv
      (fun _ hz ↦ kernel_denominator_ne_zero hz ((mem_disk_iff _).mp hw).le)).pow 2
  hermitian z _ w _ := by simp [kernel, star_mul]
  squareIntegrable z hz := (memLp_kernel_top hz).mono_exponent le_top
  reproduces f hf hfi z hz :=
    integral_kernel_mul_eq hf ((show MemLp f 2 diskArea from hfi).integrable (by norm_num)) hz

end BergmanWeakType
