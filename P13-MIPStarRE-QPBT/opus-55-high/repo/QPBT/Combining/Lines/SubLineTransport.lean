module

public import QPBT.Combining.Lines.SubLinePrefix

/-!
# Uniformity under the identification of the two scalar fields

The extended line of the sub-line construction lives over the scalar field of
the directly indexed extended game, while the two source lines live over the
scalar field of the Pauli basis test.  The two fields are identified
coordinatewise by a field isomorphism, so that identification is a bijection
of the coordinate spaces and therefore carries uniform laws to uniform laws.
This module records that transport for a whole extended point and for the two
source blocks of an extended point, and it records the resampling rule that
reading a function at the point of a uniformly random affine parameter on the
line through the canonical representative of a uniformly random point is the
same as reading that function at a uniformly random point.

## References

The statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The identification of the two scalar fields as a bijection -/

variable (P : AdmissibleParams)

/-- The coordinatewise identification of the extended scalar field with the
source scalar field on one source block, presented as a bijection.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
noncomputable def directBlockToPauliEquiv :
    (Fin P.m → DirectScalarQ P.extendedDirectLd) ≃ (Fin P.m → PauliScalar P) where
  toFun v := fun i => extendedDirectScalarEquiv P (v i)
  invFun v := fun i => (extendedDirectScalarEquiv P).symm (v i)
  left_inv v := by
    rfl
  right_inv v := by
    rfl

/-! ## Transport of the uniform laws -/

/-- The two source blocks of a uniformly random extended point, read in the
source scalar field, are independent and uniformly random.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_projX_projZ_pauli :
    (uniformDistribution
          (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)).map
        (fun u => (projX (directPointToPauli P u),
          projZ (directPointToPauli P u))) =
      Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
        (uniformDistribution (Fin P.m → PauliScalar P)) := by
  have hfun :
      (fun u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd =>
          (projX (directPointToPauli P u), projZ (directPointToPauli P u))) =
        fun u => (Equiv.prodCongr (directBlockToPauliEquiv P)
          (directBlockToPauliEquiv P)) (projX u, projZ u) := rfl
  rw [hfun, ← Distribution.map_map _ (fun u => (projX u, projZ u)),
    uniformDistribution_map_projX_projZ, ← uniformDistribution_prod,
    uniformDistribution_map_equiv, uniformDistribution_prod]

/-! ## Resampling a uniform point along a line -/

/-- Reading a function at the point of a uniformly random affine parameter on
the line through the canonical representative, in a fixed direction, of a
uniformly random point is the same as reading that function at a uniformly
random point.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_lineRepMap_add_smul_comp {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} {γ : Type*} [DecidableEq γ]
    (v : Fin m → K) (g : (Fin m → K) → γ) :
    (Distribution.prod (uniformDistribution (Fin m → K))
          (uniformDistribution K)).map
        (fun w => g (lineRepMap v w.1 + w.2 • v)) =
      (uniformDistribution (Fin m → K)).map g := by
  rw [← uniformDistribution_prod,
    ← Distribution.map_map _ (fun w : (Fin m → K) × K =>
      lineRepMap v w.1 + w.2 • v) g,
    uniformDistribution_map_lineRepMap_add_smul]

end

end MIPStarRE.QPBT
