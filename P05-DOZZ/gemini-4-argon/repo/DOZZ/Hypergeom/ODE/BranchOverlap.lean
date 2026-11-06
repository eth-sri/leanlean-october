/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneSeriesAgreement
public import DOZZ.Hypergeom.ODE.NegativeCutPlaneSeriesAgreement
public import Mathlib.Analysis.Complex.Convex

/-! The two regular branches agree on their upper and lower half-plane overlaps. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs



/-- The two selected continuations agree wherever both cut planes contain a nonreal point. -/
theorem gaussBranches_eq_of_im_ne_zero
    a b c (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z : ℂ} (hz : z.im ≠ 0) :
    gaussCutPlaneScalarState a b c z = gaussNegativeCutPlaneScalarState a b c z := by
  have gaussBranches_eq_on_lowerHalfPlane : EqOn (gaussCutPlaneScalarState a b c) (gaussNegativeCutPlaneScalarState a b c) {z : ℂ | z.im < 0} := by
    let z₀ : ℂ := -(1 / 2 : ℝ) * Complex.I
    have hnear : gaussCutPlaneScalarState a b c =ᶠ[𝓝 z₀]
        gaussNegativeCutPlaneScalarState a b c := by
      filter_upwards [Metric.ball_mem_nhds z₀ (show (0 : ℝ) < 1 / 4 by norm_num)] with z hz
      have hdist : ‖z - z₀‖ < 1 / 4 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have himnorm : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
      have himupper : (z - z₀).im < 1 / 4 := by
        have habsUpper : (z - z₀).im ≤ |(z - z₀).im| := le_abs_self _
        linarith
      have himneg : z.im < 0 := by
        rw [(show z.im = z₀.im + (z - z₀).im by rw [(show (z - z₀).im = z.im - z₀.im by simp)]; ring), (show z₀.im = -(1 / 2 : ℝ) by norm_num [z₀, Complex.mul_im])]
        linarith
      have htriangle : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
        calc
          ‖z‖ = ‖(z - z₀) + z₀‖ := by congr 1; abel
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      have hz₀norm : ‖z₀‖ = (1 / 2 : ℝ) := by norm_num [z₀]
      have hznorm : ‖z‖ < 1 := by linarith
      calc
        gaussCutPlaneScalarState a b c z = ordinaryHypergeometric a b c z :=
          gaussCutPlaneScalarState_eq_ordinary_on_unitDisk a b c hc (Or.inl (ne_of_lt himneg)) hznorm
        _ = gaussNegativeCutPlaneScalarState a b c z :=
          (gaussNegativeCutPlaneScalarState_eq_ordinary_on_unitDisk
            a b c hc (Or.inl (ne_of_lt himneg)) hznorm).symm
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (by intro z hz; apply (gaussCutPlaneScalarState_differentiableOn a b c).analyticAt; exact gaussCutPlane_isOpen.mem_nhds (Or.inl (ne_of_lt hz))) (by intro z hz; apply (gaussNegativeCutPlaneScalarState_differentiableOn a b c).analyticAt; exact gaussNegativeCutPlane_isOpen.mem_nhds (Or.inl (ne_of_lt hz))) ((Complex.isConnected_of_lowerHalfPlane (r := (0 : ℝ)) (s := ({z : ℂ | z.im < 0})) (by intro z hz; change z.im < 0 at hz; exact hz) (by intro z hz; change z.im < 0 at hz; exact le_of_lt hz)).isPreconnected) (by change z₀.im < 0; norm_num [z₀, Complex.mul_im]) hnear
  have gaussBranches_eq_on_upperHalfPlane : EqOn (gaussCutPlaneScalarState a b c) (gaussNegativeCutPlaneScalarState a b c) {z : ℂ | 0 < z.im} := by
    let z₀ : ℂ := (1 / 2 : ℝ) * Complex.I
    have hnear : gaussCutPlaneScalarState a b c =ᶠ[𝓝 z₀]
        gaussNegativeCutPlaneScalarState a b c := by
      filter_upwards [Metric.ball_mem_nhds z₀ (show (0 : ℝ) < 1 / 4 by norm_num)] with z hz
      have hdist : ‖z - z₀‖ < 1 / 4 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have himnorm : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
      have himlower : -(1 / 4 : ℝ) < (z - z₀).im := by
        have habsLower : -|(z - z₀).im| ≤ (z - z₀).im := neg_abs_le _
        linarith
      have himpos : 0 < z.im := by
        rw [(show z.im = z₀.im + (z - z₀).im by rw [(show (z - z₀).im = z.im - z₀.im by simp)]; ring), (show z₀.im = (1 / 2 : ℝ) by norm_num [z₀, Complex.mul_im])]
        linarith
      have htriangle : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
        calc
          ‖z‖ = ‖(z - z₀) + z₀‖ := by congr 1; abel
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      have hz₀norm : ‖z₀‖ = (1 / 2 : ℝ) := by norm_num [z₀]
      have hznorm : ‖z‖ < 1 := by linarith
      calc
        gaussCutPlaneScalarState a b c z = ordinaryHypergeometric a b c z :=
          gaussCutPlaneScalarState_eq_ordinary_on_unitDisk a b c hc (Or.inl (ne_of_gt himpos)) hznorm
        _ = gaussNegativeCutPlaneScalarState a b c z :=
          (gaussNegativeCutPlaneScalarState_eq_ordinary_on_unitDisk
            a b c hc (Or.inl (ne_of_gt himpos)) hznorm).symm
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (by intro z hz; apply (gaussCutPlaneScalarState_differentiableOn a b c).analyticAt; exact gaussCutPlane_isOpen.mem_nhds (Or.inl (ne_of_gt hz))) (by intro z hz; apply (gaussNegativeCutPlaneScalarState_differentiableOn a b c).analyticAt; exact gaussNegativeCutPlane_isOpen.mem_nhds (Or.inl (ne_of_gt hz))) ((Complex.isConnected_of_upperHalfPlane (r := (0 : ℝ)) (s := ({z : ℂ | 0 < z.im})) (by intro z hz; change 0 < z.im at hz; exact hz) (by intro z hz; change 0 < z.im at hz; exact le_of_lt hz)).isPreconnected) (by change 0 < z₀.im; norm_num [z₀, Complex.mul_im]) hnear
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · exact gaussBranches_eq_on_lowerHalfPlane hneg
  · exact gaussBranches_eq_on_upperHalfPlane hpos

end DOZZ.Proofs
