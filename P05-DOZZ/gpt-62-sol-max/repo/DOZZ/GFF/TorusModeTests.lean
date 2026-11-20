/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.LocalEnergyBound
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# DOZZ.GFF.TorusModeTests

Compactly supported real sine and cosine modes for the concrete periodic boxes used in G5.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped InnerProductSpace Topology

namespace DOZZ

/-- A smooth cutoff which equals one on the ball of radius `R + 1` and vanishes outside the ball
of radius `R + 2`. -/
noncomputable def localTorusCutoff (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℂ) where
  rIn := R + 1
  rOut := R + 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

section
variable (R : ℝ) (hR : 0 < R)

theorem localTorusCutoff_eq_one {z : ℂ}
    (hz : z ∈ closedBall 0 (R + 1)) : localTorusCutoff R hR z = 1 := by
  apply (localTorusCutoff R hR).one_of_mem_closedBall
  assumption

theorem localTorusCutoff_tsupport :
    tsupport (localTorusCutoff R hR : ℂ → ℝ) = closedBall 0 (R + 2) := by
  simpa [localTorusCutoff] using (localTorusCutoff R hR).tsupport_eq

end

/-- The physical phase of the `k`th Fourier mode on a square of side `L`. -/
noncomputable def torusModePhase (L : ℝ) (k : Fin 2 → ℤ) (z : ℂ) : ℝ :=
  (2 * Real.pi / L) * ((k 0 : ℝ) * z.re + (k 1 : ℝ) * z.im)

theorem torusModePhase_contDiff (L : ℝ) (k : Fin 2 → ℤ) :
    ContDiff ℝ ⊤ (torusModePhase L k) := by
  have hre : ContDiff ℝ ⊤ (fun z : ℂ => z.re) := by
    apply Complex.reCLM.contDiff
  have him : ContDiff ℝ ⊤ (fun z : ℂ => z.im) := by
    apply Complex.imCLM.contDiff
  unfold torusModePhase
  fun_prop (disch := assumption)

theorem localTorusCutoff_mul_support (R : ℝ) (hR : 0 < R) (f : ℂ → ℝ) :
    Function.support ((localTorusCutoff R hR : ℂ → ℝ) * f) ⊆ closedBall 0 (R + 2) :=
  (subset_tsupport _).trans (tsupport_mul_subset_left.trans (localTorusCutoff_tsupport R hR).subset)

noncomputable def localTorusModeTest (R : ℝ) (hR : 0 < R) (f : ℂ → ℝ)
    (hf : ContDiff ℝ ⊤ f) : TestFn :=
  TestFunction.mk ((localTorusCutoff R hR : ℂ → ℝ) * f)
    ((localTorusCutoff R hR).contDiff.mul (hf.of_le (by simp)))
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (R + 2))
      (localTorusCutoff_mul_support R hR f)) (by simp)

/-- The cosine mode, multiplied by the local compact cutoff. -/
noncomputable def localTorusCosTest (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) : TestFn :=
  localTorusModeTest R hR _ (torusModePhase_contDiff L k).cos

/-- The sine mode, multiplied by the local compact cutoff. -/
noncomputable def localTorusSinTest (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) : TestFn :=
  localTorusModeTest R hR _ (torusModePhase_contDiff L k).sin

section
variable (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) (z : ℂ)

@[simp]
theorem localTorusCosTest_apply :
    localTorusCosTest R L hR k z =
      localTorusCutoff R hR z * Real.cos (torusModePhase L k z) := rfl

@[simp]
theorem localTorusSinTest_apply :
    localTorusSinTest R L hR k z =
      localTorusCutoff R hR z * Real.sin (torusModePhase L k z) := rfl

end

private theorem localTorusCutoff_mul_abs_le_one (R : ℝ) (hR : 0 < R) (z : ℂ) {r : ℝ}
    (hr : |r| ≤ 1) : |localTorusCutoff R hR z * r| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg ((localTorusCutoff R hR).nonneg' z)]
  simpa using mul_le_mul (localTorusCutoff R hR).le_one hr (abs_nonneg r) zero_le_one

/-- The L² mass of a test bounded by one is at most the volume of the integration ball. -/
theorem torusTest_integral_sq_le_volume (R : ℝ) (f : TestFn) (hf : ∀ z, |f z| ≤ 1) :
    (∫ z in ball (0 : ℂ) (R + 3), ‖f z‖ ^ 2) ≤ (volume (ball (0 : ℂ) (R + 3))).toReal := by
  let B := ball (0 : ℂ) (R + 3)
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  calc
    _ ≤ ∫ _ in B, (1 : ℝ) ∂volume := integral_mono_of_nonneg
      (ae_of_all _ fun _ => sq_nonneg _) (integrable_const _)
      (ae_of_all _ fun z => by rw [sq_le_one_iff_abs_le_one, abs_norm]; exact hf z)
    _ = _ := by simp [B, Measure.real_def]

section
variable (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ)

theorem localTorusCosTest_support_subset :
    Function.support (localTorusCosTest R L hR k) ⊆ ball (0 : ℂ) (R + 3) :=
  (localTorusCutoff_mul_support R hR _).trans (closedBall_subset_ball (show R + 2 < R + 3 by linarith))

theorem localTorusCosTest_abs_le_one
    (z : ℂ) : |localTorusCosTest R L hR k z| ≤ 1 :=
  localTorusCutoff_mul_abs_le_one R hR z (Real.abs_cos_le_one _)

theorem localTorusSinTest_support_subset :
    Function.support (localTorusSinTest R L hR k) ⊆ ball (0 : ℂ) (R + 3) :=
  (localTorusCutoff_mul_support R hR _).trans (closedBall_subset_ball (show R + 2 < R + 3 by linarith))

theorem localTorusSinTest_abs_le_one
    (z : ℂ) : |localTorusSinTest R L hR k z| ≤ 1 :=
  localTorusCutoff_mul_abs_le_one R hR z (Real.abs_sin_le_one _)

end

end DOZZ

end
