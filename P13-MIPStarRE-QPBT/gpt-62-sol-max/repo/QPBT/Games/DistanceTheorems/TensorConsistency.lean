module

public import QPBT.Games.DistanceTheorems
public import QPBT.Games.DistanceTheorems.TensorState

/-! # Consistency under independent additive convolution

Adding the outcomes of an independently perfectly correlated ancillary measurement
pair preserves the consistency defect. The four register types are independent;
`prodShuffle` places the two registers of each player next to one another.

These are formalization-only auxiliary identities. Perfect ancillary correlation
is a hypothesis of the generic result, to be proved for the Pauli measurements
before applying it to the expanded point construction.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-438`,
  the expanded state and the convolution formula for expanded point effects.
- The same paper, `lem:qld-construct-the-paulis`.
- Blueprint `def:expanded-state` and `def:expanded-point-measurement`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#266; the ideal-point specialization is the separate issue
  Dengnifer/MIPStarRE-QPBT-bak#267.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

section Factorization

variable {ιA ιB κA κB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]

/-- For positive ancillary effects, the real joint expectation factors on the
shuffled tensor state. No normalization or positivity of `A` and `B` is needed. -/
theorem stateQForm_prodShuffle_vecTensor_heteroKron
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (φ : EuclideanSpace ℂ (κA × κB))
    (A : Op ιA) (B : Op ιB) {R : Op κA} {T : Op κB}
    (hR : 0 ≤ R) (hT : 0 ≤ T) :
    stateQForm (reindexState prodShuffle (vecTensor ψ φ))
        (heteroKron (heteroKron A R) (heteroKron B T)) =
      stateQForm ψ (heteroKron A B) * stateQForm φ (heteroKron R T) := by
  rw [stateQForm_reindexState, reindexOp_prodShuffle_heteroKron]
  exact stateQForm_vecTensor_right_hermitian _ _ _ _
    (heteroKron_isHermitian (Matrix.nonneg_iff_posSemidef.mp hR).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp hT).isHermitian)

end Factorization

/-- Applying a common injective relabeling conditioned on a perfectly
correlated ancillary answer does not change the matching mass. -/
theorem sum_matched_shift {X C Y : Type*} [Fintype X] [Fintype C] [DecidableEq Y]
    (shift : X → C → Y) (hinj : ∀ c, Function.Injective (shift · c))
    (w : X → X → ℝ) (q : C → C → ℝ)
    (hoff : ∀ c d, c ≠ d → q c d = 0) (hq : ∑ c, q c c = 1) :
    (∑ p : X × C, ∑ r : X × C,
      if shift p.1 p.2 = shift r.1 r.2 then w p.1 r.1 * q p.2 r.2 else 0) =
      ∑ a, w a a := by
  classical
  simp_rw [Fintype.sum_prod_type]
  have collapse (a b : X) (c : C) :
      (∑ d, if shift a c = shift b d then w a b * q c d else 0) =
      (if a = b then w a a * q c c else 0) := by
    rw [Fintype.sum_eq_single c]
    · by_cases hab : a = b
      · simp [hab]
      · rw [if_neg (fun h => hab (hinj c h)), if_neg hab]
    · intro d hd
      simp [hoff c d hd.symm]
  simp_rw [collapse, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum, hq, mul_one]

set_option maxHeartbeats 800000 in
/-- A common shift by perfectly correlated ancillary outcomes preserves the
mismatch mass. Unused state coordinates may be absent or included in `ψ`. -/
theorem bipartiteDefect_tensor_shift_eq
    {X G C Y I J K L : Type*}
    [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
    [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (μ : Distribution X) (A : X → Measurement G I) (B : X → Measurement G J)
    (R : X → Measurement C K) (T : X → Measurement C L)
    (ψ : EuclideanSpace ℂ (I × J)) (φ : EuclideanSpace ℂ (K × L))
    (hφ : ‖φ‖ = 1) (shift : G → C → Y)
    (hinj : ∀ c, Function.Injective (shift · c))
    (hzero : ∀ x c d, c ≠ d → stateQForm φ (heteroKron ((R x).effect c) ((T x).effect d)) = 0)
    (hdiag : ∀ x, ∑ c, stateQForm φ (heteroKron ((R x).effect c) ((T x).effect c)) = 1) :
    bipartiteDefect μ (fun x => (tensorMeasurement (A x) (R x)).postprocess (fun p => shift p.1 p.2))
      (fun x => (tensorMeasurement (B x) (T x)).postprocess (fun p => shift p.1 p.2))
      (reindexState prodShuffle (vecTensor ψ φ)) = bipartiteDefect μ A B ψ := by
  simp only [bipartiteDefect, consistencyDefect, placed_product_stateQForm_eq]
  apply avgOver_congr
  intro x
  rw [point_placed_defect_eq, point_placed_defect_eq,
    reindexState_norm_eq, vecTensor_norm_eq, hφ, mul_one,
    diagonal_postprocess_stateQForm_eq_pair_sum]
  congr 1
  have hf (a b : G × C) : stateQForm (reindexState prodShuffle (vecTensor ψ φ))
      (heteroKron ((tensorMeasurement (A x) (R x)).effect a)
        ((tensorMeasurement (B x) (T x)).effect b)) =
      stateQForm ψ (heteroKron ((A x).effect a.1) ((B x).effect b.1)) *
      stateQForm φ (heteroKron ((R x).effect a.2) ((T x).effect b.2)) :=
    stateQForm_prodShuffle_vecTensor_heteroKron ψ φ _ _ ((R x).pos a.2) ((T x).pos b.2)
  simp_rw [hf]
  exact sum_matched_shift shift hinj
    (fun a b => stateQForm ψ (heteroKron ((A x).effect a) ((B x).effect b)))
    (fun c d => stateQForm φ (heteroKron ((R x).effect c) ((T x).effect d))) (hzero x) (hdiag x)

end MIPStarRE.QPBT
