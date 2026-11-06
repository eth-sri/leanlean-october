
import GS.NonmanifoldClosure.TopologicalClosure


set_option backward.isDefEq.respectTransparency false
/-!
# Topological singularities of the original three-factor GS family

The public statements here use the scalar perfect shuffle and consecutive
block sizes `2, q, 2` from `GS.localFamily`.  A point is non-Euclidean in the
actual subspace topology; no differentiability or homology assumption is
made.

The general theorem does not require determinant one.  An explicit
Householder matrix supplies a non-Euclidean point in every size `2q`, `q ≥ 3`.
Thus the conclusion is instantiated for all dimensions in the theorem, not
only for the first example `q = 3`.
-/

noncomputable section

open Matrix

namespace GS.Results





variable (q : ℕ)

/-- Reflection perpendicular to the all-ones vector: `I - (2/q) J`.
The formula is defined also for `q = 0`; its uses below assume `q > 0`. -/
def reflectionBase  : Mat q :=
  fun i j => (if i = j then 1 else 0) - 2 / (q : ℝ)

theorem reflectionBase_apply  (i j : Fin q) :
    reflectionBase q i j = (if i = j then 1 else 0) - 2 / (q : ℝ) := rfl

theorem reflectionBase_symmetric  :
    (reflectionBase q)ᵀ = reflectionBase q := by aesop (add norm [reflectionBase_apply])

theorem reflectionBase_mul_self  (hq : 0 < q) :
    reflectionBase q * reflectionBase q = 1 := by
  let C : Mat q := fun _ _ => 2 / (q : ℝ)
  have hqR : (q : ℝ) ≠ 0 := by aesop
  have hC : C * C = C + C := by
    ext i j
    simp [C, Matrix.mul_apply]
    field_simp [hqR]
    ring
  change (1 - C) * (1 - C) = 1
  simp only [sub_mul, mul_sub, one_mul, mul_one, hC]
  abel

/-- Orthogonality is certified by an exact matrix identity, without numerical
approximation or a dimension-specific computation. -/
theorem reflectionBase_orthogonal  (hq : 0 < q) :
    Orthogonal (reflectionBase q) := by simp_all [Orthogonal.of_transpose_mul,reflectionBase_mul_self,reflectionBase_symmetric]

theorem reflectionBase_entries_ne_zero  (hq : 3 ≤ q)
    (i j : Fin q) : reflectionBase q i j ≠ 0 := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  rw [reflectionBase_apply]
  split_ifs <;> intro hz
  all_goals field_simp [hq0] at hz
  all_goals linarith





end GS.Results
