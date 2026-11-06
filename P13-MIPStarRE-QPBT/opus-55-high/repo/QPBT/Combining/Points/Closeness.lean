module

public import QPBT.Combining.Points.Orthonormalization

/-!
# Closeness estimates for the combined point measurements

Given projective measurements `Q^{x,z}` on each player's expanded local space
that are close to the sandwich POVMs on the placements where they were
constructed, this file assembles the three conclusions of `lem:qld-4-10` on
every pair of opposite placements by the triangle inequality along
`Q ≈ R ≈ M^Z M^X ≈ M^X M^Z` and the cross-placement consistency of the
ordered products.  It also records the bound `4` on the averaged squared
state-dependent distance of two families satisfying `∑ a, (A a)ᴴ * A a ≤ 1`
and `∑ a, (B a)ᴴ * B a ≤ 1` at every question, used when the test error
exceeds one, and the elementary estimate collapsing the error terms `ε`,
`√ε`, and `(ε + √ε)^{1/4}` into a single power `ε^{1/8}` when `ε ≤ 1`.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:838-881`
(self-consistency and consistency with `M̂` in the proof of `lem:qld-4-10`),
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:803-960`; the route
is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## The trivial bound -/

/-- The averaged squared state-dependent distance of two families is at most
`4` on a unit vector, under a uniform distribution, provided the sums
`∑ a, (A x a)ᴴ * A x a` and `∑ a, (B x a)ᴴ * B x a` are at most the identity
for every question `x`. -/
theorem opFamilyDistSq_uniform_le_four {X α ι : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype α] [Fintype ι] [DecidableEq ι]
    (A B : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hA : ∀ x, ∑ a, (A x a)ᴴ * A x a ≤ 1) (hB : ∀ x, ∑ a, (B x a)ᴴ * B x a ≤ 1) :
    opFamilyDistSq (uniformDistribution X) A B ψ ≤ 4 :=
  (avgOver_mono _ _ _ fun x => sum_norm_sub_apply_sq_le_four (A x) (B x) ψ hψ (hA x) (hB x)).trans_eq
    (avgOver_uniform_const _)

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι] (A : Measurement α ι)

/-- The products `A_a B_b` of the effects of two projective measurements on a
common space satisfy `∑ a b, (A_a B_b)ᴴ * (A_a B_b) = 1`. -/
theorem sum_mul_conjTranspose_mul_self_eq_one (B : Measurement β ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ ab : α × β, (A.effect ab.1 * B.effect ab.2)ᴴ * (A.effect ab.1 * B.effect ab.2) =
      1 := by
  simp only [Fintype.sum_prod_type_right, Matrix.conjTranspose_mul,
    (hA _).isSelfAdjoint.isHermitian.eq, (hB _).isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc (A.effect _) (A.effect _), (hA _).isIdempotentElem.eq, ← Finset.mul_sum,
    ← Finset.sum_mul, A.sum_eq_one, one_mul, (hB _).isIdempotentElem.eq, B.sum_eq_one]

/-- The products `B_b A_a` of the effects of two projective measurements on a
common space, indexed by the pair `(a, b)`, satisfy
`∑ a b, (B_b A_a)ᴴ * (B_b A_a) = 1`. -/
theorem sum_mul_conjTranspose_mul_self_eq_one' (B : Measurement β ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ ab : α × β, (B.effect ab.2 * A.effect ab.1)ᴴ * (B.effect ab.2 * A.effect ab.1) =
      1 := by
  have h := sum_mul_conjTranspose_mul_self_eq_one B A hB hA
  rw [Fintype.sum_prod_type, Finset.sum_comm] at h
  simpa only [Fintype.sum_prod_type] using h

/-! ## Collapsing the error terms into one power -/

/-- For `0 ≤ ε ≤ 1`, the error terms `ε`, `√ε`, and `(C₀ (ε + √ε))^{1/4}`
with `C₀ ≥ 1` are all bounded by multiples of `ε^{1/8}`. -/
theorem error_terms_le_rpow_eighth {ε C₀ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hC₀ : 1 ≤ C₀) :
    ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧ Real.sqrt ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧
      Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) ≤
        2 * C₀ * Real.rpow ε (1 / 8 : ℝ) := by
  have h1 : ε ≤ √ε := (Real.le_sqrt hε hε).mpr (by nlinarith)
  rw [Real.sqrt_eq_rpow] at h1 ⊢
  refine ⟨Real.self_le_rpow_of_le_one hε hε1 (by norm_num),
    Real.rpow_le_rpow_of_exponent_ge' hε hε1 (by norm_num) (by norm_num), ?_⟩
  calc Real.rpow (C₀ * (ε + ε ^ (1 / 2 : ℝ))) (1 / 4 : ℝ)
      ≤ (2 * C₀ * ε ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (mul_nonneg (by linarith) (by positivity)) (by nlinarith) (by norm_num)
    _ = (2 * C₀) ^ (1 / 4 : ℝ) * ε ^ (1 / 8 : ℝ) := by
        rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul hε]; norm_num
    _ ≤ 2 * C₀ * ε ^ (1 / 8 : ℝ) := by
        gcongr; exact Real.rpow_le_self_of_one_le (by linarith) (by norm_num)

end

end MIPStarRE.QPBT
