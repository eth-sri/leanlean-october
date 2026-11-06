/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
/-! The four real coefficients of the Gauss connection matrix. -/
@[expose] public section
namespace DOZZ.Proofs

noncomputable abbrev realGaussConnection₀₀ (a b c : ℝ) : ℝ :=
  Real.Gamma c * Real.Gamma (c - a - b) * (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹

noncomputable abbrev realGaussConnection₀₁ (a b c : ℝ) : ℝ :=
  Real.Gamma c * Real.Gamma (a + b - c) * (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹

noncomputable abbrev realGaussConnection₁₀ (a b c : ℝ) : ℝ :=
  Real.Gamma (2 - c) * Real.Gamma (c - a - b) * (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹

noncomputable abbrev realGaussConnection₁₁ (a b c : ℝ) : ℝ :=
  Real.Gamma (2 - c) * Real.Gamma (a + b - c) * (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹


/-- Real connection coefficients agree with the complex Gamma coefficients on the real axis. -/
theorem realGaussConnection₀₀_cast (a b c : ℝ) :
    (realGaussConnection₀₀ a b c : ℂ) =
      Complex.Gamma (c : ℂ) * Complex.Gamma ((c : ℂ) - a - b) *
      (Complex.Gamma ((c : ℂ) - a))⁻¹ * (Complex.Gamma ((c : ℂ) - b))⁻¹ := by
  simp only [realGaussConnection₀₀, Complex.ofReal_mul, Complex.ofReal_inv,
    ← Complex.Gamma_ofReal, Complex.ofReal_sub]

theorem realGaussConnection₀₁_cast (a b c : ℝ) :
    (realGaussConnection₀₁ a b c : ℂ) =
      Complex.Gamma (c : ℂ) * Complex.Gamma ((a : ℂ) + b - c) *
      (Complex.Gamma (a : ℂ))⁻¹ * (Complex.Gamma (b : ℂ))⁻¹ := by
  simp only [realGaussConnection₀₁, Complex.ofReal_mul, Complex.ofReal_inv,
    ← Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_add]

theorem realGaussConnection₁₀_cast (a b c : ℝ) :
    (realGaussConnection₁₀ a b c : ℂ) =
      Complex.Gamma (2 - (c : ℂ)) * Complex.Gamma ((c : ℂ) - a - b) *
      (Complex.Gamma (1 - (a : ℂ)))⁻¹ * (Complex.Gamma (1 - (b : ℂ)))⁻¹ := by
  simp only [realGaussConnection₁₀, Complex.ofReal_mul, Complex.ofReal_inv,
    ← Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.ofReal_one]

theorem realGaussConnection₁₁_cast (a b c : ℝ) :
    (realGaussConnection₁₁ a b c : ℂ) =
      Complex.Gamma (2 - (c : ℂ)) * Complex.Gamma ((a : ℂ) + b - c) *
      (Complex.Gamma ((a : ℂ) - c + 1))⁻¹ * (Complex.Gamma ((b : ℂ) - c + 1))⁻¹ := by
  simp only [realGaussConnection₁₁, Complex.ofReal_mul, Complex.ofReal_inv,
    ← Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_ofNat, Complex.ofReal_one]

end DOZZ.Proofs
