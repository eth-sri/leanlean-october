/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.KernelIntegrability
import BergmanWeakType.Domain
import BergmanWeakType.Rigidity.PolarIntegral
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import BergmanWeakType.Derivative



open Set Metric MeasureTheory Real
open scoped ComplexConjugate

namespace BergmanWeakType

/-- The explicit unit-disk kernel satisfies the standard Bergman-kernel characterization. -/
theorem isBergmanKernel_disk : IsBergmanKernel disk kernel
    where
  holomorphic w hw := by
    fun_prop (disch := intro z hz; exact kernel_denominator_ne_zero_closed_left ((mem_disk_iff z).mp hz).le hw) [kernel]
  hermitian z _ w _ := by simp [kernel, star_mul]
  squareIntegrable z
    hz := by
    change MemLp _ 2 diskArea
    simpa using
      MemLp.of_bound (measurable_weightedKernel 0).aestronglyMeasurable _
        ((ae_mem_disk_weightedArea 0).mono fun w hw ↦ norm_weightedKernel_le neg_one_lt_zero hz hw)
  reproduces f hf hfi z
    hz := by
    have hfi := (show MemLp f 2 diskArea from hfi).integrable one_le_two
    change ∫ w, kernel z w * f w ∂diskArea = f z
    have hz1 := (mem_disk_iff z).mp hz
    have hcircle {r} (hr : 0 < r) (hr1 : r < 1) :
      circleAverage (fun w ↦ kernel z w * f w) 0 r = f (r ^ 2 * z) + r ^ 2 * z * deriv f (r ^ 2 * z) :=
      by
      let a := r ^ 2 * z
      have ha : a ∈ ball 0 r := by
        simp [a, abs_of_pos hr]
        nlinarith
      have hsub : closedBall 0 r ⊆ disk := by
        intro w hw
        exact lt_of_le_of_lt hw hr1
      rw [circleAverage_eq_circleIntegral hr.ne']
      have hintegrand : ∀ w ∈ sphere 0 r, (w - 0)⁻¹ • (kernel z w * f w) = ((w - a) ^ 2)⁻¹ • (w * f w) :=
        by
        intro w hw
        have hwstar : w * conj w = r ^ 2 := by simp_all [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        simp [kernel, ← starRingEnd_apply]
        grind
      rw [circleIntegral.integral_congr hr.le hintegrand,
        Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
          (f := fun w ↦ w * f w) isOpen_ball hsub (differentiableOn_id.mul hf) ha,
        deriv_fun_mul (c := fun w : ℂ ↦ w) differentiableAt_id
          (hf.differentiableAt (isOpen_ball.mem_nhds (hsub (ball_subset_closedBall ha)))),
        deriv_id'', one_mul]
    have hmap : MapsTo (fun y : ℝ ↦ y * z) unitInterval disk :=
      by
      intro y hy
      apply (mem_disk_iff _).mpr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) hy.2).trans_lt hz1
    have hderiv y (hy : y ∈ unitInterval) :
      HasDerivAt (fun s : ℝ ↦ s * f (s * z)) (f (y * z) + y * z * deriv f (y * z)) y := by
      have := (hf.differentiableAt (isOpen_ball.mem_nhds (hmap hy))).hasDerivAt
      apply HasDerivAt.comp_ofReal (e := fun s ↦ s * f (s * z))
      differentiate
    have hcont := (hf.continuousOn.add (continuousOn_id.mul (hf.analyticOnNhd isOpen_ball).deriv.continuousOn)).comp (by fun_prop)
          hmap
    rw [integral_diskArea_eq_circleAverage_sqrt
        (by simpa using! integrable_weightedKernel_mul  neg_one_lt_zero (by simp_all) hz)]
    calc
      _ = ∫ y in unitIoo, f (y * z) + y * z * deriv f (y * z) :=
        by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        dsimp only
        rw [hcircle (sqrt_pos.mpr hy.1) ((sqrt_lt' zero_lt_one).mpr (by simp_all))]
        simp [← Complex.ofReal_pow, sq_sqrt hy.1.le]
      _ = f z := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
        simpa using
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy ↦ hderiv y (by simp_all))
            (hcont.intervalIntegrable_of_Icc zero_le_one)

end BergmanWeakType
