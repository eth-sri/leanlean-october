module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

@[expose] section

namespace OAI

/-!
# Descent of rational linear systems

A rational linear system which has a real solution also has a rational solution.
The proof applies a rational-linear projection from the reals onto the rationals.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- A rational-linear functional on the reals taking `1` to `1`. -/
theorem exists_ratLinear_one :
    ∃ p : ℝ →ₗ[ℚ] ℚ, p 1 = 1 :=
  Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℝ) ≠ 0)

/-- A rational-linear projection from the reals to the rationals. -/
theorem exists_ratLinear_retraction :
    ∃ p : ℝ →ₗ[ℚ] ℚ, ∀ q : ℚ, p (q : ℝ) = q := by
  obtain ⟨p, hp⟩ := exists_ratLinear_one
  refine ⟨p, fun q ↦ ?_⟩
  have h := p.map_smul q (1 : ℝ)
  simpa [hp] using h

end MatrixMultiplication.AuxiliarySeparation

end OAI
