/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionAdmissible
public import DOZZ.Statements.Defs.TestFn
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Smooth compactly supported test transport through the punctured inversion chart. -/

@[expose] public section

open Filter Topology Set Metric
open scoped Distributions

namespace DOZZ.Proofs

/-- The planar Jacobian pullback of a real test function by complex inversion. -/
noncomputable def inversionTestFunction (f : ℂ → ℝ) (x : ℂ) : ℝ :=
  f x⁻¹ * (‖x‖ ^ 2)⁻¹ ^ 2

/-- A test supported away from zero remains compactly supported after Jacobian pullback. -/
theorem inversionTestFunction_hasCompactSupport (f : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart) :
    HasCompactSupport (inversionTestFunction f) := by
  apply HasCompactSupport.of_support_subset_isCompact (f.hasCompactSupport.image_of_continuousOn (continuousOn_inv₀.mono hf))
  intro x hx
  exact ⟨x⁻¹, subset_tsupport _ (by intro h; exact hx (by simp [inversionTestFunction, h])), inv_inv x⟩

/-- A Jacobian pullback of a smooth compact test is smooth at the omitted point as well:
it vanishes in a neighborhood of zero because the original test has bounded support. -/
theorem inversionTestFunction_contDiff (f : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart) :
    ContDiff ℝ (⊤ : ℕ∞) (inversionTestFunction f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      f.hasCompactSupport.isBounded
    let B := max R 0 + 1
    have hB : 0 < B := by dsimp [B]; positivity
    have hR' : ∀ y ∈ tsupport (f : ℂ → ℝ), ‖y‖ < B := by
      intro y hy
      have h := hR hy
      rw [mem_closedBall, dist_zero_right] at h
      exact h.trans_lt (by dsimp [B]; linarith [le_max_left R 0])
    have hf0 : f 0 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have := hf h
      simp [inversionChart] at this
    have heq : inversionTestFunction f =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hB)] with y hy
      by_cases hy0 : y = 0
      · simp [inversionTestFunction, hy0, hf0]
      · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
        simp [inversionTestFunction, image_eq_zero_of_notMem_tsupport (by intro h; exact (not_lt_of_gt (by rw [norm_inv]; exact (lt_inv_comm₀ hB hyn).mpr (by simpa [mem_ball, dist_zero_right] using hy))) (hR' _ h))]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hcomp : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => f y⁻¹) x :=
      f.contDiff.contDiffAt.comp x (contDiffAt_inv ℝ hx)
    exact hcomp.mul ((((contDiff_norm_sq ℝ).contDiffAt).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).pow 2)

/-- The actual compact test representing the inverted local field evaluation. -/
noncomputable def inversionTest (f : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart) : TestFn where
  toFun := inversionTestFunction f
  contDiff' := inversionTestFunction_contDiff f hf
  hasCompactSupport' := inversionTestFunction_hasCompactSupport f hf
  tsupport_subset' := Set.subset_univ _

end DOZZ.Proofs
