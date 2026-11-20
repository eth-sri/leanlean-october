module

public import QPBT.Games.DistributionProduct

public import QPBT.Combining.Lines.SubLineConstruct

/-!
# The projected marginals of the sub-line law

This module identifies the two projected point marginals of the sub-line law
of `lem:qld-sublines` as mixtures of the restricted product laws.  The two
source lines of a sampled triple depend on the drawn extended point only
through the canonical representatives of its two source blocks, and those
representatives are unchanged when the drawn point is replaced by any point of
the extended line; a uniform point of the extended line through a uniform
point is a uniform point, so the drawn point may be replaced throughout by the
point that is finally retained.  The six generating blocks of the resulting
law -- the two source point blocks, the two scalar seeds and the two source
direction blocks -- are then regrouped into the two restricted product laws
carried by the two indices of the branch.

## References

The identification is the last step of the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Source lines depend on the point block only through its representative -/

/-- Two source lines of the same branch with the same seed and the same source
direction block agree as soon as their point blocks have the same canonical
representative in the direction of that line.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineSourceLine_congr (P : AdmissibleParams) (kind : LineKind)
    (b b' : PauliPoint P) (s : ScalarQ P.toLdParams)
    (d : PauliPoint P)
    (h : lineRepMap
        (subLineSourceDirection P kind (chiIndex P.toLdParams s) d) b =
      lineRepMap
        (subLineSourceDirection P kind (chiIndex P.toLdParams s) d) b') :
    subLineSourceLine P kind b s d = subLineSourceLine P kind b' s d := by
  cases kind
  · exact lineDesc_axis_congr h _ _
  · exact lineDesc_diagonal_congr h rfl _ _ _ _

/-! ## Generating form of the restricted product components -/

/-- The restricted line-point law of a kind at an index is the law of the
source line of that kind decoded from a uniform point block, a scalar seed in
the coordinate-index fiber of the index and a uniform direction block,
together with that same point block.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrictedLinePointDist_eq_map_prod (P : AdmissibleParams)
    (kind : LineKind) (i : Fin P.m) :
    restrictedLinePointDist P kind i =
      (Distribution.prod (uniformDistribution (PauliPoint P))
          (Distribution.prod (subLineSeedDist P i)
            (uniformDistribution (PauliPoint P)))).map
        (fun w => (subLineSourceLine P kind w.1 w.2.1 w.2.2, w.1)) := rfl

/-! ## The joint projected marginal of one branch at one extended coordinate -/

private abbrev LineSampleBlock (L : LdParams) :=
  (LdPoint L) × ScalarQ L × (LdPoint L)

/-- At a fixed line kind and a fixed extended coordinate, the joint law of the
two source lines of a sampled triple together with the two source blocks of a
uniform point of its extended line is the law of the two source lines decoded
from two independent restricted blocks together with their two point blocks.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchSamplingData_map_joint (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) :
    (Distribution.prod (subLineBlocksDist P k)
        (uniformDistribution (DirectScalarQ P.extendedDirectLd))).map
      (fun p => subLineJointProjection (subLineTripleOf P kind k p.1,
        (subLineTripleOf P kind k p.1).1.base + p.2 • (subLineTripleOf P kind k p.1).1.direction)) =
      subLineComponentProduct P (kind, subLineXIndex P k, subLineZIndex P k) := by
  classical
  let U := uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)
  let T := uniformDistribution (DirectScalarQ P.extendedDirectLd)
  let V := uniformDistribution (PauliPoint P)
  let sx := subLineSeedDist P (subLineXIndex P k)
  let sz := subLineSeedDist P (subLineZIndex P k)
  let project (y : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) :=
    (projX (directPointToPauli P y), projZ (directPointToPauli P y))
  let assemble (z : LineSampleBlock P.toLdParams × LineSampleBlock P.toLdParams) :=
    ((subLineSourceLine P kind z.1.1 z.1.2.1 z.1.2.2, z.1.1),
      (subLineSourceLine P kind z.2.1 z.2.2.1 z.2.2.2, z.2.1))
  let sample (r : (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) ×
      (ScalarQ P.toLdParams × ScalarQ P.toLdParams)) y :=
    assemble (((project y).1, r.2.1, (project r.1).1), ((project y).2, r.2.2, (project r.1).2))
  have hproj : U.map project = Distribution.prod V V := uniformDistribution_map_projX_projZ_pauli P
  have hU : uniformDistribution (SubLinePointDir P) = Distribution.prod U U := uniformDistribution_prod _ _
  simp only [subLineComponentProduct, restrictedLinePointDist_eq_map_prod, Distribution.prod_map_prodMap]
  change (Distribution.prod (Distribution.prod (uniformDistribution (SubLinePointDir P))
    (Distribution.prod sx sz)) T).map _ =
    (Distribution.prod (Distribution.prod V (Distribution.prod sx V))
      (Distribution.prod V (Distribution.prod sz V))).map assemble
  rw [hU, Distribution.prod_map_shuffleAssoc, Distribution.map_map, Distribution.prod_map_eq_bind]
  calc
    _ = (Distribution.prod (Distribution.prod U (Distribution.prod sx sz)) U).map (fun w => sample w.1 w.2) := by
      rw [Distribution.prod_map_eq_bind]
      refine Distribution.bind_congr_support _ _ _ fun r hr => ?_
      obtain ⟨-, hx, hz⟩ := by simpa only [Distribution.prod_support, Finset.mem_product] using hr
      have hx := subLineSeedDist_index hx
      have hz := subLineSeedDist_index hz
      let v := subLineExtDirection P kind k r.1
      rw [← uniformDistribution_map_lineRepMap_add_smul_comp v (sample r)]
      congr 1
      funext y
      dsimp only [Function.comp_def, sample, assemble, project]
      change (((subLineSourceLine P kind (projX (directPointToPauli P y.1)) r.2.1 _, _),
          (subLineSourceLine P kind (projZ (directPointToPauli P y.1)) r.2.2 _, _))) = _
      rw [show (subLineTripleOf P kind k ((y.1, r.1), r.2)).1.base = lineRepMap v y.1 from
          subLineExtLine_base P kind k _,
        show (subLineTripleOf P kind k ((y.1, r.1), r.2)).1.direction = v from
          subLineExtLine_direction P kind k _]
      apply Prod.ext <;> apply Prod.ext <;> try rfl
      · apply subLineSourceLine_congr
        rw [hx]
        exact (subLineProject_representative P .X kind k y.1 r.1 y.2).symm
      · apply subLineSourceLine_congr
        rw [hz]
        exact (subLineProject_representative P .Z kind k y.1 r.1 y.2).symm
    _ = _ := by
      rw [← Distribution.prod_map_transposeTriple, Distribution.map_map, ← hproj,
        Distribution.prod_map_left U (Distribution.prod sx sz) project, Distribution.prod_map_prodMap,
        Distribution.map_map]
      rfl

end

end MIPStarRE.QPBT
