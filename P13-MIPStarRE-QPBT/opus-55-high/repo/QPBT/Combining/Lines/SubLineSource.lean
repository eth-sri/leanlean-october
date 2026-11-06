module

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
    (b b' : Fin P.m → PauliScalar P) (s : ScalarQ P.toLdParams)
    (d : Fin P.m → PauliScalar P)
    (h : lineRepMap
        (subLineSourceDirection P kind (chiIndex P.toLdParams s) d) b =
      lineRepMap
        (subLineSourceDirection P kind (chiIndex P.toLdParams s) d) b') :
    subLineSourceLine P kind b s d = subLineSourceLine P kind b' s d := by
  cases kind
  · exact lineDesc_axis_congr h _ _
  · exact lineDesc_diagonal_congr h rfl _ _ _ _

variable (P : AdmissibleParams) (kind : LineKind) (k : Fin (2 * P.m + 2))

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
      (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
          (Distribution.prod (subLineSeedDist P i)
            (uniformDistribution (Fin P.m → PauliScalar P)))).map
        (fun w => (subLineSourceLine P kind w.1 w.2.1 w.2.2, w.1)) := by
  cases kind
  · show restrictedALineDist P.toLdParams i = _
    rw [restrictedALineDist_eq_map_prod, freshDiagonalPairDist_eq_prod]
    rfl
  · show restrictedDLineDist P.toLdParams i = _
    rw [restrictedDLineDist_eq_map_prod, freshDiagonalPairDist_eq_prod]
    rfl

/-- The `X` component law of a pair of indices is the law of the two source
lines decoded from two independent restricted blocks, together with the point
block of the first.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineXComponentDist_eq_map_prod (P : AdmissibleParams)
    (kind : LineKind) (i j : Fin P.m) :
    subLineXComponentDist P (kind, (i, j)) =
      (Distribution.prod
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
            (Distribution.prod (subLineSeedDist P i)
              (uniformDistribution (Fin P.m → PauliScalar P))))
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
            (Distribution.prod (subLineSeedDist P j)
              (uniformDistribution (Fin P.m → PauliScalar P))))).map
        (fun w => ((subLineSourceLine P kind w.1.1 w.1.2.1 w.1.2.2,
          subLineSourceLine P kind w.2.1 w.2.2.1 w.2.2.2), w.1.1)) := by
  simp only [subLineXComponentDist, restrictedLinePointDist_eq_map_prod,
    Distribution.map_map]
  rw [Distribution.prod_map_left, Distribution.prod_map_right,
    Distribution.map_map, Distribution.map_map]

/-- The `Z` component law of a pair of indices is the law of the two source
lines decoded from two independent restricted blocks, together with the point
block of the second.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineZComponentDist_eq_map_prod (P : AdmissibleParams)
    (kind : LineKind) (i j : Fin P.m) :
    subLineZComponentDist P (kind, (i, j)) =
      (Distribution.prod
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
            (Distribution.prod (subLineSeedDist P i)
              (uniformDistribution (Fin P.m → PauliScalar P))))
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
            (Distribution.prod (subLineSeedDist P j)
              (uniformDistribution (Fin P.m → PauliScalar P))))).map
        (fun w => ((subLineSourceLine P kind w.1.1 w.1.2.1 w.1.2.2,
          subLineSourceLine P kind w.2.1 w.2.2.1 w.2.2.2), w.2.1)) := by
  simp only [subLineZComponentDist, restrictedLinePointDist_eq_map_prod,
    Distribution.map_map]
  rw [Distribution.prod_map_left, Distribution.prod_map_right,
    Distribution.map_map, Distribution.map_map]

/-! ## The joint projected marginal of one branch at one extended coordinate -/

/-- At a fixed line kind and a fixed extended coordinate, the joint law of the
two source lines of a sampled triple together with the two source blocks of a
uniform point of its extended line is the law of the two source lines decoded
from two independent restricted blocks together with their two point blocks.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchSamplingData_map_joint :
    (Distribution.prod
        (Distribution.prod (uniformDistribution (SubLinePointDir P))
          (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
            (subLineSeedDist P (subLineZIndex P k))))
        (uniformDistribution (DirectScalarQ P.extendedDirectLd))).map
      (fun p => ((subLineTripleOf P kind k p.1).2,
        (projX (directPointToPauli P
            ((subLineTripleOf P kind k p.1).1.base +
              p.2 • (subLineTripleOf P kind k p.1).1.direction)),
          projZ (directPointToPauli P
            ((subLineTripleOf P kind k p.1).1.base +
              p.2 • (subLineTripleOf P kind k p.1).1.direction))))) =
      (Distribution.prod
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (uniformDistribution (Fin P.m → PauliScalar P))))
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
            (Distribution.prod (subLineSeedDist P (subLineZIndex P k))
              (uniformDistribution (Fin P.m → PauliScalar P))))).map
        (fun w => ((subLineSourceLine P kind w.1.1 w.1.2.1 w.1.2.2,
          subLineSourceLine P kind w.2.1 w.2.2.1 w.2.2.2),
          (w.1.1, w.2.1))) := by
  have hshuffle :
      Distribution.prod
          (Distribution.prod (uniformDistribution (SubLinePointDir P))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k))))
          (uniformDistribution (DirectScalarQ P.extendedDirectLd)) =
      (Distribution.prod
          (Distribution.prod
            (uniformDistribution
              (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k))))
          (Distribution.prod
            (uniformDistribution
              (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))
            (uniformDistribution
              (DirectScalarQ P.extendedDirectLd)))).map
        (fun w => (((w.2.1, w.1.1), w.1.2), w.2.2)) := by
    rw [show uniformDistribution (SubLinePointDir P) = _ from uniformDistribution_prod _ _]
    refine (Distribution.map_bijective_eq _ _
      (fun w : ((_ × _ × _) × _ × _) => (((w.2.1, w.1.1), w.1.2), w.2.2))
      (fun u : (((_ × _) × _ × _) × _) => ((u.1.1.2, u.1.2), (u.1.1.1, u.2)))
      (fun _ => rfl) (fun _ => rfl)
      (fun _ => by simp only [Distribution.prod_support, Finset.mem_product]; tauto)
      (fun _ => by simp only [Distribution.prod_weight]; ring)).symm
  have hpp2 :
      (Distribution.prod
          (Distribution.prod
            (uniformDistribution
              (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k))))
          (uniformDistribution
            (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))).map
        (fun w => ((subLineSourceLine P kind
              (projX (directPointToPauli P w.2)) w.1.2.1
              (projX (directPointToPauli P w.1.1)),
            subLineSourceLine P kind
              (projZ (directPointToPauli P w.2)) w.1.2.2
              (projZ (directPointToPauli P w.1.1))),
          (projX (directPointToPauli P w.2),
            projZ (directPointToPauli P w.2)))) =
      (Distribution.prod
          (Distribution.prod
            (Distribution.prod
              (uniformDistribution (Fin P.m → PauliScalar P))
              (uniformDistribution (Fin P.m → PauliScalar P)))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k))))
          (Distribution.prod
            (uniformDistribution (Fin P.m → PauliScalar P))
            (uniformDistribution (Fin P.m → PauliScalar P)))).map
        (fun w => ((subLineSourceLine P kind w.2.1 w.1.2.1 w.1.1.1,
            subLineSourceLine P kind w.2.2 w.1.2.2 w.1.1.2),
          (w.2.1, w.2.2))) := by
    simp only [← uniformDistribution_map_projX_projZ_pauli, Distribution.prod_map_left,
      Distribution.prod_map_right, Distribution.map_map]
  have hfinal :
      (Distribution.prod
          (Distribution.prod
            (Distribution.prod
              (uniformDistribution (Fin P.m → PauliScalar P))
              (uniformDistribution (Fin P.m → PauliScalar P)))
            (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
              (subLineSeedDist P (subLineZIndex P k))))
          (Distribution.prod
            (uniformDistribution (Fin P.m → PauliScalar P))
            (uniformDistribution (Fin P.m → PauliScalar P)))).map
        (fun w => ((w.2.1, (w.1.2.1, w.1.1.1)),
          (w.2.2, (w.1.2.2, w.1.1.2)))) =
      Distribution.prod
        (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
          (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
            (uniformDistribution (Fin P.m → PauliScalar P))))
        (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
          (Distribution.prod (subLineSeedDist P (subLineZIndex P k))
            (uniformDistribution (Fin P.m → PauliScalar P)))) := by
    refine Distribution.map_bijective_eq _ _
      (fun w : (((_ × _) × _ × _) × _ × _) =>
        ((w.2.1, (w.1.2.1, w.1.1.1)), (w.2.2, (w.1.2.2, w.1.1.2))))
      (fun u : ((_ × _ × _) × _ × _ × _) =>
        (((u.1.2.2, u.2.2.2), (u.1.2.1, u.2.2.1)), (u.1.1, u.2.1)))
      (fun _ => rfl) (fun _ => rfl)
      (fun _ => by simp only [Distribution.prod_support, Finset.mem_product]; tauto)
      (fun _ => by simp only [Distribution.prod_weight]; ring)
  rw [hshuffle]
  refine Eq.trans (Distribution.map_map _ _ _) ?_
  refine Eq.trans (Distribution.prod_map_eq_bind _ _ _) ?_
  refine Eq.trans (Distribution.bind_congr_support _ _
    (fun r => (uniformDistribution
        (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)).map
      (fun y => ((subLineSourceLine P kind (projX (directPointToPauli P y))
            r.2.1 (projX (directPointToPauli P r.1)),
          subLineSourceLine P kind (projZ (directPointToPauli P y))
            r.2.2 (projZ (directPointToPauli P r.1))),
        (projX (directPointToPauli P y),
          projZ (directPointToPauli P y))))) ?_) ?_
  · intro r hr
    obtain ⟨-, hseeds⟩ := Finset.mem_product.mp hr
    obtain ⟨hsx, hsz⟩ := Finset.mem_product.mp hseeds
    have hx : chiIndex P.toLdParams r.2.1 = subLineXIndex P k :=
      (Finset.mem_filter.mp hsx).2
    have hz : chiIndex P.toLdParams r.2.2 = subLineZIndex P k :=
      (Finset.mem_filter.mp hsz).2
    refine (congrArg (Distribution.map _) (funext fun p => ?_)).trans
      (uniformDistribution_map_lineRepMap_add_smul_comp (subLineExtDirection P kind k r.1)
        (fun y => ((subLineSourceLine P kind (projX (directPointToPauli P y))
            r.2.1 (projX (directPointToPauli P r.1)),
          subLineSourceLine P kind (projZ (directPointToPauli P y))
            r.2.2 (projZ (directPointToPauli P r.1))),
        (projX (directPointToPauli P y), projZ (directPointToPauli P y)))))
    simp only [subLineTripleOf, subLineExtLine_base, subLineExtLine_direction]
    refine Prod.ext (Prod.ext ?_ ?_) rfl <;> refine subLineSourceLine_congr P kind _ _ _ _ ?_
    · rw [hx]
      exact (lineRepMap_proj_lineRepMap_add_smul P projX projX_add projX_smul _ _ _ _
        (projX_subLineExtDirection_mem_span P kind k r.1)).symm
    · rw [hz]
      exact (lineRepMap_proj_lineRepMap_add_smul P projZ projZ_add projZ_smul _ _ _ _
        (projZ_subLineExtDirection_mem_span P kind k r.1)).symm
  · refine ((Distribution.prod_map_eq_bind _ _ _).symm.trans hpp2).trans ?_
    rw [← hfinal, Distribution.map_map]

/-! ## The two one-point projected marginals of one branch -/

/-- At a fixed line kind and a fixed extended coordinate, the joint law of the
two source lines of a sampled triple together with the source `X` block of a
uniform point of its extended line is the `X` component law of the two indices
of that branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchSamplingData_map_projX :
    (Distribution.prod
        (Distribution.prod (uniformDistribution (SubLinePointDir P))
          (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
            (subLineSeedDist P (subLineZIndex P k))))
        (uniformDistribution (DirectScalarQ P.extendedDirectLd))).map
      (fun p => ((subLineTripleOf P kind k p.1).2,
        projX (directPointToPauli P
          ((subLineTripleOf P kind k p.1).1.base +
            p.2 • (subLineTripleOf P kind k p.1).1.direction)))) =
      subLineXComponentDist P
        (kind, (subLineXIndex P k, subLineZIndex P k)) := by
  have h := congrArg
    (fun D : Distribution ((LineDesc P.toLdParams × LineDesc P.toLdParams) ×
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))) =>
      Distribution.map D (fun z => (z.1, z.2.1)))
    (subLineBranchSamplingData_map_joint P kind k)
  simp only [Distribution.map_map] at h
  refine Eq.trans h ?_
  exact (subLineXComponentDist_eq_map_prod P kind (subLineXIndex P k)
    (subLineZIndex P k)).symm

/-- At a fixed line kind and a fixed extended coordinate, the joint law of the
two source lines of a sampled triple together with the source `Z` block of a
uniform point of its extended line is the `Z` component law of the two indices
of that branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchSamplingData_map_projZ :
    (Distribution.prod
        (Distribution.prod (uniformDistribution (SubLinePointDir P))
          (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
            (subLineSeedDist P (subLineZIndex P k))))
        (uniformDistribution (DirectScalarQ P.extendedDirectLd))).map
      (fun p => ((subLineTripleOf P kind k p.1).2,
        projZ (directPointToPauli P
          ((subLineTripleOf P kind k p.1).1.base +
            p.2 • (subLineTripleOf P kind k p.1).1.direction)))) =
      subLineZComponentDist P
        (kind, (subLineXIndex P k, subLineZIndex P k)) := by
  have h := congrArg
    (fun D : Distribution ((LineDesc P.toLdParams × LineDesc P.toLdParams) ×
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))) =>
      Distribution.map D (fun z => (z.1, z.2.2)))
    (subLineBranchSamplingData_map_joint P kind k)
  simp only [Distribution.map_map] at h
  refine Eq.trans h ?_
  exact (subLineZComponentDist_eq_map_prod P kind (subLineXIndex P k)
    (subLineZIndex P k)).symm

end

end MIPStarRE.QPBT
