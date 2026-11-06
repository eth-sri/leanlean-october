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

/-- Replacing the drawn extended point by a point of the extended line does
not change the canonical representative of its `X` block in the direction of
the source `X` line of the branch.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineRepMap_projX_subLineExtLine_point (P : AdmissibleParams)
    (kind : LineKind) (k : Fin (2 * P.m + 2))
    (x e : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)
    (t : DirectScalarQ P.extendedDirectLd) :
    lineRepMap
        (subLineSourceDirection P kind (subLineXIndex P k)
          (projX (directPointToPauli P e)))
        (projX (directPointToPauli P
          (lineRepMap (subLineExtDirection P kind k e) x +
            t • subLineExtDirection P kind k e))) =
      lineRepMap
        (subLineSourceDirection P kind (subLineXIndex P k)
          (projX (directPointToPauli P e)))
        (projX (directPointToPauli P x)) := by
  rw [← lineRepMap_projX_directPointToPauli_lineRepMap P _ _ _
      (projX_subLineExtDirection_mem_span P kind k e),
    ← lineRepMap_projX_directPointToPauli_lineRepMap P _ x _
      (projX_subLineExtDirection_mem_span P kind k e),
    lineRepMap_add_smul, lineRepMap_apply_self]

theorem lineRepMap_projZ_subLineExtLine_point (P : AdmissibleParams)
    (kind : LineKind) (k : Fin (2 * P.m + 2))
    (x e : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)
    (t : DirectScalarQ P.extendedDirectLd) :
    lineRepMap
        (subLineSourceDirection P kind (subLineZIndex P k)
          (projZ (directPointToPauli P e)))
        (projZ (directPointToPauli P
          (lineRepMap (subLineExtDirection P kind k e) x +
            t • subLineExtDirection P kind k e))) =
      lineRepMap
        (subLineSourceDirection P kind (subLineZIndex P k)
          (projZ (directPointToPauli P e)))
        (projZ (directPointToPauli P x)) := by
  rw [← lineRepMap_projZ_directPointToPauli_lineRepMap P _ _ _
      (projZ_subLineExtDirection_mem_span P kind k e),
    ← lineRepMap_projZ_directPointToPauli_lineRepMap P _ x _
      (projZ_subLineExtDirection_mem_span P kind k e),
    lineRepMap_add_smul, lineRepMap_apply_self]

/-! ## Generating form of the restricted product components -/

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

theorem subLineBranchSamplingData_map_joint (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) :
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
  classical
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
    rw [show uniformDistribution (SubLinePointDir P) =
      Distribution.prod
        (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))
        (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)) from
      uniformDistribution_prod _ _]
    symm
    refine Distribution.map_bijective_eq _ _ _
      (fun u => ((u.1.1.2, u.1.2), (u.1.1.1, u.2))) (fun _ => rfl) (fun _ => rfl)
      (fun _ => by simp only [Distribution.prod_support, Finset.mem_product]; tauto)
      (fun _ => by simp only [Distribution.prod_weight]; ring)
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
    rw [← uniformDistribution_map_projX_projZ_pauli,
      Distribution.prod_map_left _
        (Distribution.prod (subLineSeedDist P (subLineXIndex P k))
          (subLineSeedDist P (subLineZIndex P k)))
        (fun u => (projX (directPointToPauli P u), projZ (directPointToPauli P u))),
      Distribution.prod_map_right _ _
        (fun u => (projX (directPointToPauli P u), projZ (directPointToPauli P u))),
      Distribution.prod_map_left _ _ _,
      Distribution.map_map, Distribution.map_map]
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
            (uniformDistribution (Fin P.m → PauliScalar P)))) :=
    Distribution.map_bijective_eq _ _ _
      (fun u => (((u.1.2.2, u.2.2.2), (u.1.2.1, u.2.2.1)), (u.1.1, u.2.1)))
      (fun _ => rfl) (fun _ => rfl)
      (fun _ => by simp only [Distribution.prod_support, Finset.mem_product]; tauto)
      (fun _ => by simp only [Distribution.prod_weight]; ring)
  rw [hshuffle, Distribution.map_map, Distribution.prod_map_eq_bind,
    ← hfinal, Distribution.map_map]
  erw [← hpp2, Distribution.prod_map_eq_bind]
  refine Distribution.bind_congr_support _ _ _ fun r hr => ?_
  obtain ⟨-, hseeds⟩ := Finset.mem_product.mp hr
  obtain ⟨hsx, hsz⟩ := Finset.mem_product.mp hseeds
  have hx : chiIndex P.toLdParams r.2.1 = subLineXIndex P k := (Finset.mem_filter.mp hsx).2
  have hz : chiIndex P.toLdParams r.2.2 = subLineZIndex P k := (Finset.mem_filter.mp hsz).2
  refine (congrArg (Distribution.map _) (funext fun p => ?_)).trans
    (uniformDistribution_map_lineRepMap_add_smul_comp
      (subLineExtDirection P kind k r.1)
      (fun y => ((subLineSourceLine P kind (projX (directPointToPauli P y))
            r.2.1 (projX (directPointToPauli P r.1)),
          subLineSourceLine P kind (projZ (directPointToPauli P y))
            r.2.2 (projZ (directPointToPauli P r.1))),
        (projX (directPointToPauli P y), projZ (directPointToPauli P y)))))
  dsimp only [subLineTripleOf]
  rw [subLineExtLine_base P kind k ((p.1, r.1), r.2),
    subLineExtLine_direction P kind k ((p.1, r.1), r.2)]
  refine Prod.ext (Prod.ext ?_ ?_) rfl
  · refine subLineSourceLine_congr P kind _ _ _ _ ?_
    rw [hx]
    exact (lineRepMap_projX_subLineExtLine_point P kind k p.1 r.1 p.2).symm
  · refine subLineSourceLine_congr P kind _ _ _ _ ?_
    rw [hz]
    exact (lineRepMap_projZ_subLineExtLine_point P kind k p.1 r.1 p.2).symm

/-! ## The two one-point projected marginals of one branch -/

/-- At a fixed line kind and a fixed extended coordinate, the joint law of the
two source lines of a sampled triple together with the source `X` block of a
uniform point of its extended line is the `X` component law of the two indices
of that branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchSamplingData_map_projX (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) :
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
  classical
  have h := congrArg (Distribution.map · (fun z => (z.1, z.2.1)))
    (subLineBranchSamplingData_map_joint P kind k)
  simp only [Distribution.map_map] at h
  rw [h, subLineXComponentDist]
  simp only [restrictedLinePointDist_eq_map_prod, Distribution.map_map,
    Distribution.prod_map_left, Distribution.prod_map_right]

theorem subLineBranchSamplingData_map_projZ (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) :
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
  classical
  have h := congrArg (Distribution.map · (fun z => (z.1, z.2.2)))
    (subLineBranchSamplingData_map_joint P kind k)
  simp only [Distribution.map_map] at h
  rw [h, subLineZComponentDist]
  simp only [restrictedLinePointDist_eq_map_prod, Distribution.map_map,
    Distribution.prod_map_left, Distribution.prod_map_right]

end

end MIPStarRE.QPBT
