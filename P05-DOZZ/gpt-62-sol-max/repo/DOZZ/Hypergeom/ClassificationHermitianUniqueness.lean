/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! A nonzero Wronskian makes a Hermitian tensor unique from its mixed Wirtinger jet. -/

@[expose] public section

namespace DOZZ.Proofs

private theorem two_by_two_eq_zero {a b c d x y : ℂ} (h : a * d - c * b ≠ 0)
    (h₁ : a * x + b * y = 0) (h₂ : c * x + d * y = 0) : x = 0 ∧ y = 0 := by
  grind (splits := 0)

/-- The four entries of a Hermitian tensor are determined by the value, the two first Wirtinger
derivatives, and the mixed derivative at any point where the basis Wronskian is nonzero. -/
theorem hermitianTensor_coefficients_eq_of_wirtinger_jet
    (f g df dg A B C D : ℂ) (hW : f * dg - df * g ≠ 0)
    (h₀₀ : A * f * star f + B * f * star g +
      C * g * star f + D * g * star g = 0)
    (h₁₀ : A * df * star f + B * df * star g +
      C * dg * star f + D * dg * star g = 0)
    (h₀₁ : A * f * star df + B * f * star dg +
      C * g * star df + D * g * star dg = 0)
    (h₁₁ : A * df * star df + B * df * star dg +
      C * dg * star df + D * dg * star dg = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  obtain ⟨h₀, h₁⟩ := two_by_two_eq_zero (x := A * star f + B * star g)
    (y := C * star f + D * star g) hW (by linear_combination h₀₀) (by linear_combination h₁₀)
  obtain ⟨h₂, h₃⟩ := two_by_two_eq_zero (x := A * star df + B * star dg)
    (y := C * star df + D * star dg) hW (by linear_combination h₀₁) (by linear_combination h₁₁)
  have hw : star f * star dg - star df * star g ≠ 0 := by
    simpa only [star_sub, star_mul'] using star_ne_zero.mpr hW
  have ha := two_by_two_eq_zero hw (x := A) (y := B)
    (by linear_combination h₀) (by linear_combination h₂)
  grind (splits := 0)

/-- For a Hermitian off-diagonal tensor, its value and first holomorphic Wirtinger derivative
already determine the two off-diagonal entries when the basis Wronskian is nonzero. -/
theorem hermitianOffDiagonal_eq_zero_of_value_and_z_derivative
    (f g df dg B C : ℂ) (hW : f * dg - df * g ≠ 0)
    (hHerm : C = star B)
    (h₀ : B * f * star g + C * g * star f = 0)
    (h₁ : B * df * star g + C * dg * star f = 0) :
    B = 0 ∧ C = 0 := by
  obtain ⟨hBg, hCf⟩ := two_by_two_eq_zero hW (x := B * star g) (y := C * star f)
    (by linear_combination h₀) (by linear_combination h₁)
  by_cases hg : g = 0
  · have hf : f ≠ 0 := by intro hf; simp [hf, hg] at hW
    have hc := (mul_eq_zero.mp hCf).resolve_right (star_ne_zero.mpr hf)
    exact ⟨by simpa [hc] using congrArg star hHerm.symm, hc⟩
  · have hb := (mul_eq_zero.mp hBg).resolve_right (star_ne_zero.mpr hg)
    exact ⟨hb, by simp [hHerm, hb]⟩

end DOZZ.Proofs
