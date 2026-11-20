module

public import QPBT.Combining.Points.Orthonormalization
public import QPBT.Combining.Witnesses

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
    opFamilyDistSq (uniformDistribution X) A B ψ ≤ 4 := by
  unfold opFamilyDistSq
  calc _
      ≤ avgOver (uniformDistribution X) (fun _ => (4 : ℝ)) := by
        refine avgOver_mono _ _ _ fun x => ?_
        exact sum_norm_sub_apply_sq_le_four (A x) (B x) ψ hψ (hA x) (hB x)
    _ = 4 := avgOver_uniform_const _

/-! ## The chain of closeness estimates -/

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The three closeness conclusions of `lem:qld-4-10` for a pair of projective
families close to the placed sandwiches: with `η` the closeness of `Q` to `R`
on every placement, `C₁ √ε` the closeness of `R` to the ordered product,
`C₂ √ε` the commutation error, and `C₃ ε` the cross-placement consistency of
the ordered products, the distances from `Q` on one placement to the two
ordered products and to `Q` on the opposite placement are bounded by explicit
combinations.  Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:838-881`. -/
theorem chain_bounds (S : ProjectiveSetting P ε) (Q : PointPairFamily S)
    (η r c e : ℝ)
    (hQR : ∀ p : Placement, opFamilyDistSq (uniformDistribution (PointPair P))
      (S.placedPointPairFamily Q p) (S.placedPointPairFamily S.sandwichPoint p) S.psiHat ≤ η)
    (hRZ : ∀ p : Placement, opFamilyDistSq (uniformDistribution (PointPair P))
      (S.placedPointPairFamily S.sandwichPoint p) (S.placedOrderedPointProduct p .Z) S.psiHat ≤ r)
    (hXZ : ∀ p : Placement, opFamilyDistSq (uniformDistribution (PointPair P))
      (S.placedOrderedPointProduct p .X) (S.placedOrderedPointProduct p .Z) S.psiHat ≤ c)
    (hZX : ∀ p q : Placement, p.IsOpposite q → opFamilyDistSq (uniformDistribution (PointPair P))
      (S.placedOrderedPointProduct p .Z) (S.placedOrderedPointProduct q .X) S.psiHat ≤ e)
    (p q : Placement) (hop : p.IsOpposite q) :
    (∀ W, opFamilyDistSq (uniformDistribution (PointPair P)) (S.placedPointPairFamily Q p)
      (S.placedOrderedPointProduct q W) S.psiHat ≤ 4 * η + 8 * r + 8 * e + 2 * c) ∧
    opFamilyDistSq (uniformDistribution (PointPair P)) (S.placedPointPairFamily Q p)
      (S.placedPointPairFamily Q q) S.psiHat ≤ 12 * η + 20 * r + 16 * e + 4 * c := by
  have hcombine {A B C : PointPair P → PauliScalar P × PauliScalar P →
      Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)} {u v : ℝ}
      (h₁ : opFamilyDistSq (uniformDistribution (PointPair P)) A B S.psiHat ≤ u)
      (h₂ : opFamilyDistSq (uniformDistribution (PointPair P)) B C S.psiHat ≤ v) :=
    opFamilyDistSq_le_of_le_of_le _ _ _ _ _ _ _ h₁ h₂
  have hX := hcombine (hQR p) (hcombine (hRZ p) (hZX p q hop))
  have hZ := hcombine hX (hXZ q)
  have hQ := hcombine (hQR q) (hRZ q)
  rw [opFamilyDistSq_symm] at hQ
  refine ⟨fun W => ?_, (hcombine hZ hQ).trans (by linarith)⟩
  cases W
  · exact hX.trans (by linarith [opFamilyDistSq_nonneg _ _ _ _ |>.trans (hQR p),
      opFamilyDistSq_nonneg _ _ _ _ |>.trans (hRZ p),
      opFamilyDistSq_nonneg _ _ _ _ |>.trans (hXZ q),
      opFamilyDistSq_nonneg _ _ _ _ |>.trans (hZX p q hop)])
  · exact hZ.trans (by linarith)

end ProjectiveSetting

/-! ## Collapsing the error terms into one power -/

/-- For `0 ≤ ε ≤ 1`, the error terms `ε`, `√ε`, and `(C₀ (ε + √ε))^{1/4}`
with `C₀ ≥ 1` are all bounded by multiples of `ε^{1/8}`. -/
theorem error_terms_le_rpow_eighth {ε C₀ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hC₀ : 1 ≤ C₀) :
    ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧ Real.sqrt ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧
      Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) ≤
        2 * C₀ * Real.rpow ε (1 / 8 : ℝ) := by
  simp only [Real.rpow_eq_pow, Real.sqrt_eq_rpow]
  have mono {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :=
    Real.rpow_le_rpow_of_exponent_ge' hε hε1 hr hrs
  have h : ε ≤ ε ^ (1 / 2 : ℝ) := by simpa using mono (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  refine ⟨h.trans (mono (by norm_num) (by norm_num)), mono (by norm_num) (by norm_num), ?_⟩
  have hC : 0 ≤ 2 * C₀ := by linarith
  calc
    _ ≤ (2 * C₀ * ε ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ C₀)]) (by norm_num)
    _ = (2 * C₀) ^ (1 / 4 : ℝ) * ε ^ (1 / 8 : ℝ) := by
      rw [Real.mul_rpow hC (by positivity), ← Real.rpow_mul hε]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by linarith) (by norm_num)) (by positivity)

end

end MIPStarRE.QPBT
