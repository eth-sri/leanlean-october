module

public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Lean.Elab.Tactic.Omega

public section

@[expose] section

namespace OAI

/-!
# The Fourier projection has no modular wrap

Section 4.1 of *Matrix Multiplication via Auxiliary Separation and Polynomial
Multiplication* uses exactly `5 * M` Fourier phases. The exponent
`u - v + 2 * (g - h)` has absolute value at most `3 * (M - 1)` when all four
labels lie in `{1, ..., M}`. Consequently, divisibility by `5 * M` is equivalent
to the exact integer support equation.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- The explicit bound for the exponent in the finite Fourier projection. -/
theorem fourierPhase_abs_le {M h g u v : ℤ}
    (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    |u - v + 2 * (g - h)| ≤ 3 * (M - 1) := by
  rw [abs_le']
  constructor <;> omega

/-- The Fourier modulus exceeds the full possible range of the exponent. -/
theorem fourierRadius_lt_modulus {M : ℤ} (hM : 1 ≤ M) :
    3 * (M - 1) < 5 * M := by
  omega

/-- Every possible exponent lies strictly between minus and plus the modulus. -/
theorem fourierPhase_abs_lt {M h g u v : ℤ}
    (hM : 1 ≤ M) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    |u - v + 2 * (g - h)| < 5 * M :=
  lt_of_le_of_lt (fourierPhase_abs_le hh hg hu hv) (fourierRadius_lt_modulus hM)

end MatrixMultiplication.AuxiliarySeparation

end OAI
