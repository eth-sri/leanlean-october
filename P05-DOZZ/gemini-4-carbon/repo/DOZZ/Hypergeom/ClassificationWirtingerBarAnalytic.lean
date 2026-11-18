/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationWirtingerBar

/-! Regularity of conjugate Wirtinger derivatives when the conjugate function is holomorphic. -/

@[expose] public section

namespace DOZZ.Proofs

variable {U : Set ℂ}


open Filter
open scoped Topology

section
variable (hU : IsOpen U) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ (fun w => star (f w)) U) {z : ℂ} (hz : z ∈ U)
include hU hf hz

/-- If the conjugate of `f` is analytic on an open set, the conjugate Wirtinger derivative of `f`
is real-differentiable there. -/
theorem differentiableAt_wirtingerBar_of_analytic_conjugate
 :
    DifferentiableAt ℝ (fun w => wirtingerBar f w) z := by
  let h : ℂ → ℂ := fun w => star (f w)
  have hderiv : AnalyticOnNhd ℂ (deriv h) U := by
    simpa [h] using hf.deriv
  have hEq : (fun w => wirtingerBar f w) =ᶠ[𝓝 z]
      (fun w => star (deriv h w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact wirtingerBar_eq_star_deriv_of_star_differentiableAt
      (hf w hw).differentiableAt (by rfl)
  exact ((Complex.differentiable_conj.differentiableAt (x := deriv h z)).comp z (((hderiv z hz).differentiableAt).restrictScalars ℝ)).congr_of_eventuallyEq hEq

/-- Two conjugate Wirtinger derivatives are the conjugate of the second ordinary derivative
whenever the conjugate of the original function is analytic near the evaluation point. -/
theorem wirtingerBar_wirtingerBar_eq_star_deriv_deriv_of_analytic_conjugate
 :
    wirtingerBar (fun w => wirtingerBar f w) z =
      star (deriv (deriv (fun w => star (f w))) z) := by
  let h : ℂ → ℂ := fun w => star (f w)
  have hderiv : AnalyticOnNhd ℂ (deriv h) U := by
    simpa [h] using hf.deriv
  have hderivAt := (hderiv z hz).differentiableAt
  have hstarBarAt : DifferentiableAt ℝ
      (fun w => star (wirtingerBar f w)) z := by
    exact (Complex.differentiable_conj.differentiableAt (x := wirtingerBar f z)).comp z (differentiableAt_wirtingerBar_of_analytic_conjugate hU hf hz)
  have heq : (fun w => star (wirtingerBar f w)) =ᶠ[𝓝 z] deriv h := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hwEq := wirtingerBar_eq_star_deriv_of_star_differentiableAt
      (hf w hw).differentiableAt (by rfl)
    calc
      star (wirtingerBar f w) = star (star (deriv h w)) := by rw [hwEq]
      _ = deriv h w := star_star _
  change star (wirtingerZ (fun w => star (wirtingerBar f w)) z) = _
  rw [wirtingerZ_congr_of_eventuallyEq hstarBarAt (hderivAt.restrictScalars ℝ) heq, wirtingerZ_eq_deriv_of_differentiableAt hderivAt]

/-- The conjugate Wirtinger derivative of an antiholomorphic function is itself antiholomorphic. -/
theorem wirtingerZ_wirtingerBar_eq_zero_of_analytic_conjugate
 :
    wirtingerZ (fun w => wirtingerBar f w) z = 0 := by
  let h : ℂ → ℂ := fun w => star (f w)
  have hderiv : AnalyticOnNhd ℂ (deriv h) U := by
    simpa [h] using hf.deriv
  have hderivAt := (hderiv z hz).differentiableAt
  have hstarAt : DifferentiableAt ℝ (fun w => star (deriv h w)) z := by
    exact (Complex.differentiable_conj.differentiableAt (x := deriv h z)).comp z (hderivAt.restrictScalars ℝ)
  have heq : (fun w => wirtingerBar f w) =ᶠ[𝓝 z]
      (fun w => star (deriv h w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact wirtingerBar_eq_star_deriv_of_star_differentiableAt
      (hf w hw).differentiableAt (by rfl)
  exact (wirtingerZ_congr_of_eventuallyEq (differentiableAt_wirtingerBar_of_analytic_conjugate hU hf hz) hstarAt heq).trans (wirtingerZ_star_eq_zero_of_differentiableAt hderivAt)

/-- Two conjugate Wirtinger derivatives are real-differentiable when the original function's
conjugate is analytic nearby. -/
theorem differentiableAt_wirtingerBar_wirtingerBar_of_analytic_conjugate
 :
    DifferentiableAt ℝ (fun w => wirtingerBar (fun u => wirtingerBar f u) w) z := by
  let h : ℂ → ℂ := fun w => star (f w)
  have hderiv2 : AnalyticOnNhd ℂ (deriv (deriv h)) U := by
    have hderiv : AnalyticOnNhd ℂ (deriv h) U := by
      simpa [h] using hf.deriv
    exact hderiv.deriv
  have hstarAt : DifferentiableAt ℝ
      (fun w => star (deriv (deriv h) w)) z := by
    have hclm := Complex.differentiable_conj.differentiableAt
      (x := deriv (deriv h) z)
    exact hclm.comp z (((hderiv2 z hz).differentiableAt).restrictScalars ℝ)
  have hEq : (fun w => wirtingerBar (fun u => wirtingerBar f u) w) =ᶠ[𝓝 z]
      (fun w => star (deriv (deriv h) w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact wirtingerBar_wirtingerBar_eq_star_deriv_deriv_of_analytic_conjugate
      hU hf hw
  exact hstarAt.congr_of_eventuallyEq hEq

/-- The second conjugate Wirtinger derivative is antiholomorphic whenever the original function's
conjugate is analytic. -/
theorem wirtingerZ_wirtingerBar_wirtingerBar_eq_zero_of_analytic_conjugate
 :
    wirtingerZ (fun w => wirtingerBar (fun u => wirtingerBar f u) w) z = 0 := by
  let h : ℂ → ℂ := fun w => star (f w)
  have hderiv2 : AnalyticOnNhd ℂ (deriv (deriv h)) U := by
    have hderiv : AnalyticOnNhd ℂ (deriv h) U := by
      simpa [h] using hf.deriv
    exact hderiv.deriv
  have hderiv2At :=
    (hderiv2 z hz).differentiableAt
  have hstarAt : DifferentiableAt ℝ
      (fun w => star (deriv (deriv h) w)) z := by
    have hclm := Complex.differentiable_conj.differentiableAt
      (x := deriv (deriv h) z)
    exact hclm.comp z (hderiv2At.restrictScalars ℝ)
  have hEq : (fun w => wirtingerBar (fun u => wirtingerBar f u) w) =ᶠ[𝓝 z]
      (fun w => star (deriv (deriv h) w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact wirtingerBar_wirtingerBar_eq_star_deriv_deriv_of_analytic_conjugate
      hU hf hw
  have hbarbarAt : DifferentiableAt ℝ
      (fun w => wirtingerBar (fun u => wirtingerBar f u) w) z := differentiableAt_wirtingerBar_wirtingerBar_of_analytic_conjugate hU hf hz
  exact (wirtingerZ_congr_of_eventuallyEq hbarbarAt hstarAt hEq).trans (wirtingerZ_star_eq_zero_of_differentiableAt hderiv2At)


end
end DOZZ.Proofs
