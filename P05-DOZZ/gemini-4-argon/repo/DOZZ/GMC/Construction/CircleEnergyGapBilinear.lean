/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.CircleEnergyGapPositivity

/-!
# Bilinear estimates from the circle energy gap

Positivity of the gap `DOZZ.circleEnergyGap` gives a Cauchy--Schwarz estimate against any fixed
smooth test. This identifies mixed energies of two circle approximations without assuming a circle
witness.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace DOZZ.Proofs



/-- Approximation in vanishing circle gap forces mixed test energies to the circle pairing. -/
theorem tendsto_gffCov_test_circleCross_of_gap
    x r y s
    (f g : ℕ → TestFn)
    (hf : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0))
    (hg : Tendsto (fun n => circleEnergyGap y s (g n)) atTop (𝓝 0))
    (hcross : Tendsto (fun n => circleCross y s (g n)) atTop
      (𝓝 (circleSelfEnergy y s))) :
    Tendsto (fun n => gffCov (f n) (g n) - circleCross x r (g n)) atTop (𝓝 0) := by
  have circleEnergyGap_mixed_error_bound a (ha : 0 < a) f g : 2 * a * |gffCov f g - circleCross x r g| ≤ circleEnergyGap x r f + a ^ 2 * gffCov g g := by
    have circleEnergyGap_add_smul x r a f g : circleEnergyGap x r (f + a • g) = circleEnergyGap x r f + 2 * a * (gffCov f g - circleCross x r g) + a ^ 2 * gffCov g g := by
      rw [circleEnergyGap, circleEnergyGap, gffCov_add_self, gffCov_smul_self,
        circleCross_add, circleCross_smul]
      rw [(show gffCov f (a • g) = a * gffCov f g by rw [← inner_equatorKernelLimitMap_eq_gffCov, ← inner_equatorKernelLimitMap_eq_gffCov, map_smul, inner_smul_right])]
      ring
    have hplus := circleEnergyGap_nonneg x r (f + a • g)
    have hminus := circleEnergyGap_nonneg x r (f + (-a) • g)
    rw [circleEnergyGap_add_smul] at hplus hminus
    have habs := abs_le.mpr ⟨(by nlinarith), (show 2 * a * (gffCov f g - circleCross x r g) ≤ circleEnergyGap x r f + a ^ 2 * gffCov g g by nlinarith)⟩
    rw [abs_mul, abs_of_pos (by positivity)] at habs
    nlinarith
  have henergy : Tendsto (fun n => gffCov (g n) (g n)) atTop (𝓝 (circleSelfEnergy y s)) := by
    have he n : gffCov (g n) (g n) = circleEnergyGap y s (g n) +
        2 * circleCross y s (g n) - circleSelfEnergy y s := by
      rw [circleEnergyGap]
      ring
    have hl' := ((hg.add (hcross.const_mul 2)).sub_const (circleSelfEnergy y s)).congr' (Filter.Eventually.of_forall fun n => (he n).symm)
    rw [show (0 : ℝ) + 2 * circleSelfEnergy y s - circleSelfEnergy y s =
      circleSelfEnergy y s by ring] at hl'
    exact hl'
  have : 0 ≤ circleSelfEnergy y s :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds henergy
      (fun n => DOZZ.gffCov_self_nonneg (g n))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let A := circleSelfEnergy y s + 1
  have hA : 0 ≤ A := by dsimp [A]; linarith
  let a := ε / (2 * (A + 1))
  filter_upwards [(henergy.eventually (Iio_mem_nhds (by linarith)) : ∀ᶠ n in atTop, gffCov (g n) (g n) < circleSelfEnergy y s + 1), (hf.eventually (gt_mem_nhds (by positivity)) : ∀ᶠ n in atTop, circleEnergyGap x r (f n) < ε * a)] with n hnE hnq
  have := circleEnergyGap_mixed_error_bound a (by dsimp [a]; positivity) (f n) (g n)
  have hD : |gffCov (f n) (g n) - circleCross x r (g n)| < ε := by
    have hmain : ε * a + a ^ 2 * A < 2 * a * ε := by
      dsimp [a]
      field_simp
      nlinarith [hε, hA]
    nlinarith [hnq, (mul_le_mul_of_nonneg_left (by simpa [A] using hnE.le) (sq_nonneg a)), (show 0 < 2 * a by positivity), hmain]
  simpa [Real.dist_eq] using hD

end DOZZ.Proofs
