module

public import Mathlib

/-!
# The parameter `λ = arcosh(√q / 2)`

For `q > 4`, `λ = arcosh(√q/2)` is the unique `λ > 0` with `cosh λ = √q / 2`.
-/

public section

namespace PottsDiscontinuity

theorem arcosh_pos_of_gt4 (q : ℝ) (hq : 4 < q) :
    0 < Real.arcosh (Real.sqrt q / 2) ∧ Real.cosh (Real.arcosh (Real.sqrt q / 2)) = Real.sqrt q / 2 := by
  have h2 : (2:ℝ) < Real.sqrt q := by
    rw [show (2:ℝ) = Real.sqrt 4 by
      norm_num]
    simp_all
  exact ⟨Real.arcosh_pos (by linarith), Real.cosh_arcosh (by linarith)⟩

end PottsDiscontinuity
