module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

public section

@[expose] section

namespace OAI

/-!
# Entropy optimization for finitely many sectors

The normalized weights `q = A / (A + B)` and `1 - q = B / (A + B)`
make the entropy-weighted geometric mean equal to `A + B`. This is the
scalar identity used in Section 5.1 of the auxiliary-separation argument.
The same calculation also applies to an arbitrary nonempty finite family.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- The logarithmic form of the entropy identity at the normalized weights. -/
theorem binary_entropy_log_partition {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.binEntropy (A / (A + B)) +
        Real.log A * (A / (A + B)) +
        Real.log B * (1 - A / (A + B)) = Real.log (A + B) := by
  have hsum : A + B ≠ 0 := ne_of_gt (add_pos hA hB)
  have hcomplement : 1 - A / (A + B) = B / (A + B) := by
    field_simp
    ring
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  rw [hcomplement, Real.log_div hA.ne' hsum, Real.log_div hB.ne' hsum]
  field_simp
  ring

end MatrixMultiplication.AuxiliarySeparation

end OAI
