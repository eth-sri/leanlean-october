/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianWirtingerExpansion
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! The conjugated PDE and its `∂z` derivative separate the two Cramer coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

private theorem gaussOperator_analytic {a b c : ℂ} {F : ℂ → ℂ} {U : Set ℂ}
    (h : AnalyticOnNhd ℂ F U) : AnalyticOnNhd ℂ (gaussHolomorphicOperator a b c F) U := by
  intro z hz
  have hd := h.deriv z hz
  have hdd := h.deriv.deriv z hz
  have hf := h z hz
  unfold gaussHolomorphicOperator
  fun_prop

private theorem conjugate_gauss_residual (a b c : ℝ) {K : ℂ → ℂ}
    (hK : AnalyticOnNhd ℂ (fun w => star (K w)) gaussCutPlane) {z : ℂ} (hz : z ∈ gaussCutPlane) :
    wirtingerBar (fun w => wirtingerBar K w) z +
        star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) * wirtingerBar K z -
        star ((a : ℂ) * b / (z * (1 - z))) * K z =
      star (gaussHolomorphicOperator (a : ℂ) b c (fun w => star (K w)) z / (z * (1 - z))) := by
  have hreg := gaussCutPlane_subset_regularPlane hz
  have h1 : 1 - z ≠ 0 := sub_ne_zero.mpr hreg.2.symm
  rw [wirtingerBar_wirtingerBar_eq_star_deriv_deriv_of_analytic_conjugate gaussCutPlane_isOpen hK hz,
    wirtingerBar_eq_star_deriv_of_star_differentiableAt (hK z hz).differentiableAt rfl]
  apply star_injective
  simp only [star_add, star_sub, star_mul, star_star, gaussHolomorphicOperator]
  field_simp [hreg.1, h1]

/-- A holomorphic fundamental pair separates the two antiholomorphic coefficients
in a vanishing linear combination. -/
private theorem separate_conjugate_coefficients {f g F G : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane) (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hF : AnalyticOnNhd ℂ F gaussCutPlane) (hG : AnalyticOnNhd ℂ G gaussCutPlane)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0)
    (he : ∀ z ∈ gaussCutPlane, f z * star (F z) + g z * star (G z) = 0)
    : ∀ z ∈ gaussCutPlane, F z = 0 ∧ G z = 0 := by
  intro z hz
  have hloc : (fun w => f w * star (F w) + g w * star (G w)) =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [gaussCutPlane_isOpen.mem_nhds hz] with w hw using he w hw
  have hd := wirtingerZ_congr_of_eventuallyEq hloc
  have hfz := (hf z hz).differentiableAt
  have hgz := (hg z hz).differentiableAt
  have hFz := (hF z hz).differentiableAt
  have hGz := (hG z hz).differentiableAt
  rw [wirtingerZ_add (f := fun w => f w * star (F w)) (g := fun w => g w * star (G w))
    ((hfz.restrictScalars ℝ).mul (DifferentiableAt.star (hFz.restrictScalars ℝ)))
    ((hgz.restrictScalars ℝ).mul (DifferentiableAt.star (hGz.restrictScalars ℝ))),
    wirtingerZ_mul_star_of_differentiableAt hfz hFz,
    wirtingerZ_mul_star_of_differentiableAt hgz hGz] at hd
  rw [show wirtingerZ (fun _ => (0 : ℂ)) z = 0 by simp [wirtingerZ]] at hd
  have h1 : gaussCramerWronskian f g z * star (F z) = 0 := by
    unfold gaussCramerWronskian
    linear_combination deriv g z * he z hz - g z * hd
  have h2 : gaussCramerWronskian f g z * star (G z) = 0 := by
    unfold gaussCramerWronskian
    linear_combination f z * hd - deriv f z * he z hz
  exact ⟨star_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (hW z hz)),
    star_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (hW z hz))⟩

section
variable (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T) {f g : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f gaussCutPlane) (hg : AnalyticOnNhd ℂ g gaussCutPlane)
  (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
  (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
  (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0)
include a b c hT hf hg hODEf hODEg hW

/-- Conjugating the Cramer coefficients gives two holomorphic solutions of the original Gauss
ODE on the slit plane. -/
theorem realGaussCramer_conjugates_solve_gauss :
    (∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (fun w => star (gaussCramerCoefficient₁ T f g w)) z = 0) ∧
    (∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (fun w => star (gaussCramerCoefficient₂ T f g w)) z = 0) := by
  obtain ⟨hA, hB⟩ := realGaussCramer_conjugates_analytic a b c T hT hf hg hODEf hODEg hW
  let F := gaussHolomorphicOperator (a : ℂ) b c (fun w => star (gaussCramerCoefficient₁ T f g w))
  let G := gaussHolomorphicOperator (a : ℂ) b c (fun w => star (gaussCramerCoefficient₂ T f g w))
  suffices he : ∀ z ∈ gaussCutPlane, f z * star (F z) + g z * star (G z) = 0 by
    have H := separate_conjugate_coefficients hf hg (gaussOperator_analytic hA)
      (gaussOperator_analytic hB) hW he
    exact ⟨fun z hz => (H z hz).1, fun z hz => (H z hz).2⟩
  intro z hz
  have h := realGaussCramer_conjugate_pde_expansion a b c T hT hf hg hODEf hODEg hW z hz
  rw [conjugate_gauss_residual a b c hA hz, conjugate_gauss_residual a b c hB hz,
    star_div₀, star_div₀] at h
  have hreg := gaussCutPlane_subset_regularPlane hz
  have hd : z * (1 - z) ≠ 0 := mul_ne_zero hreg.1 (sub_ne_zero.mpr hreg.2.symm)
  change f z * (star (F z) / _) + g z * (star (G z) / _) = 0 at h
  rwa [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_zero_iff, star_eq_zero, or_iff_left hd] at h

/-- Each conjugate Cramer coefficient has constant coordinates in any global analytic Gauss
fundamental pair on the slit plane. -/
theorem realGaussCramer_conjugates_have_constant_basis_coordinates :
    ∃ u v : ℂ × ℂ, ∀ z ∈ gaussCutPlane,
      star (gaussCramerCoefficient₁ T f g z) = u.1 * f z + u.2 * g z ∧
      star (gaussCramerCoefficient₂ T f g z) = v.1 * f z + v.2 * g z := by
  have hconjAnalytic := realGaussCramer_conjugates_analytic
    a b c T hT hf hg hODEf hODEg hW
  have hconjODE := realGaussCramer_conjugates_solve_gauss
    a b c T hT hf hg hODEf hODEg hW
  obtain ⟨u, hu, _⟩ := gauss_two_solution_span_unique
    (a : ℂ) (b : ℂ) (c : ℂ) f g hf.differentiableOn hg.differentiableOn
    hODEf hODEg (fun z hz => hW z hz)
    (fun z => star (gaussCramerCoefficient₁ T f g z))
    hconjAnalytic.1.differentiableOn hconjODE.1
  obtain ⟨v, hv, _⟩ := gauss_two_solution_span_unique
    (a : ℂ) (b : ℂ) (c : ℂ) f g hf.differentiableOn hg.differentiableOn
    hODEf hODEg (fun z hz => hW z hz)
    (fun z => star (gaussCramerCoefficient₂ T f g z))
    hconjAnalytic.2.differentiableOn hconjODE.2
  refine ⟨u, v, ?_⟩
  intro z hz
  exact ⟨hu z hz, hv z hz⟩

end

end DOZZ.Proofs
