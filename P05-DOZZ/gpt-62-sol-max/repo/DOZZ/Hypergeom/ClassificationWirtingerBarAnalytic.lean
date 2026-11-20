/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationWirtingerBar
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! Regularity of conjugate Wirtinger derivatives when the conjugate function is holomorphic. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

private theorem wirtingerBar_eventuallyEq_star_deriv {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ (fun w => star (f w)) U) {z : ℂ} (hz : z ∈ U) :
    wirtingerBar f =ᶠ[𝓝 z] fun w => star (deriv (fun u => star (f u)) w) := by
  filter_upwards [hU.mem_nhds hz] with w hw
  exact wirtingerBar_eq_star_deriv_of_star_differentiableAt (hf w hw).differentiableAt rfl

/-- The conjugate derivative of an antiholomorphic function is real-differentiable. -/
theorem differentiableAt_wirtingerBar_of_analytic_conjugate
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ (fun w => star (f w)) U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun w => wirtingerBar f w) z :=
  (DifferentiableAt.star ((hf.deriv z hz).differentiableAt.restrictScalars ℝ)).congr_of_eventuallyEq
    (wirtingerBar_eventuallyEq_star_deriv hU hf hz)

/-- Two conjugate derivatives of an antiholomorphic function are the conjugate of its
conjugate's second ordinary derivative. -/
theorem wirtingerBar_wirtingerBar_eq_star_deriv_deriv_of_analytic_conjugate
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ (fun w => star (f w)) U) {z : ℂ} (hz : z ∈ U) :
    wirtingerBar (fun w => wirtingerBar f w) z =
      star (deriv (deriv (fun w => star (f w))) z) := by
  have he : (fun w => star (wirtingerBar f w)) =ᶠ[𝓝 z] deriv (fun w => star (f w)) := by
    filter_upwards [wirtingerBar_eventuallyEq_star_deriv hU hf hz] with w hw
    simp only [hw, star_star]
  change star (wirtingerZ (fun w => star (wirtingerBar f w)) z) = _
  rw [wirtingerZ_congr_of_eventuallyEq he, wirtingerZ_eq_deriv_of_differentiableAt
    (hf.deriv z hz).differentiableAt]

end DOZZ.Proofs
