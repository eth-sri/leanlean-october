/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Poisson supermean property of the normalized unweighted kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Complex InnerProductSpace
open scoped Topology

namespace BergmanWeakType.Weighted

theorem continuousOn_poisson_circle {R : ℝ} {z : ℂ} (hz : z ∈ Metric.ball 0 R) :
    ContinuousOn (poissonKernel 0 z) (Metric.sphere 0 |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_herglotzRieszKernel_sphere
  intro heq
  have hz' : ‖z‖ < R := by simpa using hz
  have heq' : ‖z‖ = |R| := by simpa using heq
  linarith [le_abs_self R]

theorem poisson_nonneg_on_circle {R : ℝ} {z ζ : ℂ} (hz : z ∈ Metric.ball 0 R)
    (hζ : ζ ∈ Metric.sphere 0 |R|) : 0 ≤ poissonKernel 0 z ζ := by
  have hz' : ‖z‖ < R := by simpa using hz
  have hR : 0 < R := (norm_nonneg z).trans_lt hz'
  have hζ' : ‖ζ‖ = R := by simpa [abs_of_pos hR] using hζ
  simp only [poissonKernel_def, sub_zero, hζ']
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

theorem circleAverage_poisson_re {R : ℝ} {z : ℂ} {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Metric.ball 0 R)) (hz : z ∈ Metric.ball 0 R) :
    Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * (g ζ).re) 0 R = (g z).re := by
  have hR : 0 < R := Metric.pos_of_mem_ball hz
  have hgs : ContinuousOn g (Metric.sphere 0 |R|) := by
    apply hg.continuousOn.mono
    rw [closure_ball 0 hR.ne']
    simpa only [abs_of_pos hR] using Metric.sphere_subset_closedBall
  have hi : CircleIntegrable (poissonKernel 0 z • g) 0 R :=
    ((continuousOn_poisson_circle hz).smul hgs).circleIntegrable'
  have h := Complex.reCLM.circleAverage_comp_comm hi
  rw [hg.circleAverage_poissonKernel_smul hz] at h
  simpa only [Function.comp_def, Complex.reCLM_apply, Pi.smul_apply', Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

/-- The elementary Poisson Jensen inequality for the squared norm of a holomorphic function. -/
theorem norm_sq_le_circleAverage_poisson {R : ℝ} {z : ℂ} {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Metric.ball 0 R)) (hz : z ∈ Metric.ball 0 R) :
    ‖g z‖ ^ 2 ≤ Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * ‖g ζ‖ ^ 2) 0 R := by
  let H : ℂ → ℂ := fun ζ ↦ (2 * star (g z)) * g ζ - ((‖g z‖ ^ 2 : ℝ) : ℂ)
  have hH : DiffContOnCl ℂ H (Metric.ball 0 R) :=
    (hg.const_smul (2 * star (g z))).sub_const _
  have htangent (ζ : ℂ) : (H ζ).re ≤ ‖g ζ‖ ^ 2 := by
    have hsq := sq_nonneg ((g ζ).re - (g z).re)
    have hsq' := sq_nonneg ((g ζ).im - (g z).im)
    simp only [H, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.sq_norm, Complex.normSq_apply] at *
    norm_num at *
    nlinarith
  have hHz : (H z).re = ‖g z‖ ^ 2 := by
    simp only [H, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.sq_norm, Complex.normSq_apply]
    norm_num
    ring
  have hR : 0 < R := Metric.pos_of_mem_ball hz
  have hgs : ContinuousOn g (Metric.sphere 0 |R|) := by
    apply hg.continuousOn.mono
    rw [closure_ball 0 hR.ne']
    simpa only [abs_of_pos hR] using Metric.sphere_subset_closedBall
  have hHs : ContinuousOn H (Metric.sphere 0 |R|) := by
    apply hH.continuousOn.mono
    rw [closure_ball 0 hR.ne']
    simpa only [abs_of_pos hR] using Metric.sphere_subset_closedBall
  rw [← hHz, ← circleAverage_poisson_re hH hz]
  apply Real.circleAverage_mono
    ((continuousOn_poisson_circle hz).mul (Complex.continuous_re.comp_continuousOn hHs)).circleIntegrable'
    ((continuousOn_poisson_circle hz).mul (hgs.norm.pow 2)).circleIntegrable'
  intro ζ hζ
  exact mul_le_mul_of_nonneg_left (htangent ζ) (poisson_nonneg_on_circle hz hζ)

end BergmanWeakType.Weighted
