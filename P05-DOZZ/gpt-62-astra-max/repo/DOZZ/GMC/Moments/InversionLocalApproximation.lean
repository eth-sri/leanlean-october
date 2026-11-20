/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionTest
public import DOZZ.GFFStructure.AnnularCircleEnergy

/-! Smooth circle-test approximation within the punctured inversion chart. -/

@[expose] public section

open Filter Topology Set Metric MeasureTheory
open scoped Distributions

namespace DOZZ.Proofs

/-- A compact density supported away from zero admits a smooth mask equal to one on its support
and identically zero near zero. -/
theorem exists_inversion_test_mask {g : ℂ → ℝ} (hcompact : HasCompactSupport g)
    (hU : tsupport g ⊆ inversionChart) :
    ∃ a : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, 0 ≤ a x ∧ a x ≤ 1) ∧
      (∀ x ∈ tsupport g, a x = 1) ∧ tsupport a ⊆ inversionChart := by
  have h0 : (0 : ℂ) ∉ tsupport g := by
    intro h
    have := hU h
    simp [inversionChart] at this
  have hnhds : (tsupport g)ᶜ ∈ 𝓝 (0 : ℂ) :=
    hcompact.isClosed.isOpen_compl.mem_nhds h0
  obtain ⟨δ, hδ, hδK⟩ := Metric.mem_nhds_iff.mp hnhds
  let b : ContDiffBump (0 : ℂ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let a : ℂ → ℝ := fun x => 1 - b x
  have ha : tsupport a ⊆ (ball (0 : ℂ) (δ / 4))ᶜ := by
    apply closure_minimal
    · intro x hx hxball
      have hb : b x = 1 := b.one_of_mem_closedBall (ball_subset_closedBall hxball)
      exact hx (by simp [a, hb])
    · exact isOpen_ball.isClosed_compl
  refine ⟨a, contDiff_const.sub b.contDiff, ?_, ?_, ?_⟩
  · intro x
    dsimp [a]
    exact ⟨sub_nonneg.mpr b.le_one, sub_le_self _ b.nonneg⟩
  · intro x hx
    have hout : x ∉ closedBall (0 : ℂ) (δ / 2) := by
      intro hxball
      have hxδ : x ∈ ball (0 : ℂ) δ :=
        closedBall_subset_ball (by linarith) hxball
      exact hδK hxδ hx
    have hb : b x = 0 := image_eq_zero_of_notMem_tsupport (by
      rw [b.tsupport_eq]
      exact hout)
    simp [a, hb]
  · intro x hx
    change x ≠ 0
    intro hx0
    have := ha hx
    simp [hx0, mem_ball, hδ] at this

/-- The annular circle-density approximants stay within twice the circle radius of its center.
-/
theorem tsupport_circleAnnularDensity_subset_centered (x : ℂ) (r : ℝ) (n : ℕ) :
    tsupport (circleAnnularDensity x r n) ⊆ closedBall x (2 * Real.exp (-r)) := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hρ : DOZZ.annularProbabilityDensity n ((Real.exp (-r))⁻¹ • (z - x)) ≠ 0 := by
    intro hzero
    exact hz (by simp only [circleAnnularDensity, hzero, mul_zero])
  have hb := DOZZ.annularProbabilityDensity_radius_bound n _ hρ
  have hn : 1 ≤ (n : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hi : 1 / ((n : ℝ) + 2) ≤ 1 :=
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn).trans_eq one_div_one
  have hscale : ‖(Real.exp (-r))⁻¹ • (z - x)‖ ≤ 2 := by
    linarith [(abs_lt.mp hb).2]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.exp_pos _))] at hscale
  have hmul := mul_le_mul_of_nonneg_left hscale (Real.exp_pos (-r)).le
  rw [← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul] at hmul
  simpa only [mem_closedBall, dist_eq_norm, mul_comm] using hmul

end DOZZ.Proofs
