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

variable (f : TestFn) (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart)

include f hf in
/-- A test supported away from zero remains compactly supported after Jacobian pullback. -/
theorem inversionTestFunction_hasCompactSupport  :
    HasCompactSupport (inversionTestFunction f) := by
  have hc  :=
    f.hasCompactSupport.image_of_continuousOn (continuousOn_inv₀.mono hf)
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  have hfx : f x⁻¹ ≠ 0 := by
    intro h
    exact hx (by simp [inversionTestFunction, h])
  exact ⟨x⁻¹, subset_tsupport _ hfx, inv_inv x⟩

include f hf in
/-- A Jacobian pullback of a smooth compact test is smooth at the omitted point as well:
it vanishes in a neighborhood of zero because the original test has bounded support. -/
theorem inversionTestFunction_contDiff  :
    ContDiff ℝ (⊤ : ℕ∞) (inversionTestFunction f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      f.hasCompactSupport.isBounded
    let B : ℝ := max R 0 + 1
    have hB : 0 < B := by dsimp [B]; positivity
    have hR' : ∀ y ∈ tsupport (f : ℂ → ℝ), ‖y‖ < B := by
      intro y hy
      have h := hR hy
      rw [mem_closedBall, dist_zero_right] at h
      grind
    have hf0 : f 0 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      bound
    have heq : inversionTestFunction f =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hB)] with y hy
      by_cases hy0 : y = 0
      · simp [inversionTestFunction, hy0, hf0]
      · have hyn  := norm_pos_iff.mpr hy0
        have hsmall : ‖y‖ < B⁻¹ := by simpa [mem_ball, dist_zero_right] using hy
        have hlarge : B < ‖y⁻¹‖ := by
          rw [norm_inv]
          exact (lt_inv_comm₀ hB hyn).mpr hsmall
        have hout : y⁻¹ ∉ tsupport (f : ℂ → ℝ) := by
          grind
        simp [inversionTestFunction, image_eq_zero_of_notMem_tsupport hout]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hcomp  :=
      f.contDiff.contDiffAt.comp x (contDiffAt_inv ℝ hx)
    have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => ‖y‖ ^ 2) x :=
      (contDiff_norm_sq ℝ).contDiffAt
    exact hcomp.mul ((hnorm.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).pow 2)

include f hf in
/-- The actual compact test representing the inverted local field evaluation. -/
noncomputable def inversionTest  : TestFn where
  toFun := inversionTestFunction f
  contDiff' := inversionTestFunction_contDiff f hf
  hasCompactSupport' := inversionTestFunction_hasCompactSupport f hf
  tsupport_subset' := Set.subset_univ _

end DOZZ.Proofs
