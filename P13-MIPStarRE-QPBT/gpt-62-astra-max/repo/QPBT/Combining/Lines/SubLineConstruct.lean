module

public import QPBT.Combining.Lines.SubLineBranch
public import QPBT.Combining.Lines.SubLineSeed

/-!
# The sampling procedure of the sub-line lemma

This module carries out the sampling procedure of `lem:qld-sublines`.  A line
kind is drawn from the two kinds, an extended coordinate and an extended point
and direction are drawn uniformly, and two scalar seeds are drawn
independently in the coordinate-index fibers of the two coordinates that the
two source lines must carry.  The sampled triple consists of the axis or
diagonal line of the extended sample together with the two source lines
decoded from the two coordinate blocks of the extended point and direction and
from the two seeds.

The module records the elementary evaluations of that triple, the description
of the support of the resulting law, the three pointwise properties of a
sampled triple -- incidence of the two source blocks, compatibility of the
affine data, and closure of the axis branch -- and the identification of its
extended-line marginal.

## References

The construction is the proof of `lem:qld-sublines` in
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

/-! ## The auxiliary randomness of one branch -/

/-- An extended point together with an extended direction.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
abbrev SubLinePointDir (P : AdmissibleParams) :=
  (DirectPoint P.extendedDirectLd) ×
    (DirectPoint P.extendedDirectLd)

/-- The auxiliary randomness of one branch of the sampling procedure: an
extended point, an extended direction, and the two scalar seeds of the two
source lines.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
abbrev SubLineSamplingData (P : AdmissibleParams) :=
  SubLinePointDir P × (ScalarQ P.toLdParams × ScalarQ P.toLdParams)

/-- The law of the scalar seed carried by a source line at a given coordinate
index: uniform on the coordinate-index fiber of that index.  Blueprint
`def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
noncomputable def subLineSeedDist {P : AdmissibleParams} (i : Fin P.m) :
    Distribution (ScalarQ P.toLdParams) :=
  Distribution.restrict (uniformDistribution (ScalarQ P.toLdParams))
    (ldSeedIndexEvent P.toLdParams i) (ldSeedIndexEvent_positive P.toLdParams i)

/-- Every seed law of a source line has total mass one. -/
theorem subLineSeedDist_isProbability (P : AdmissibleParams) (i : Fin P.m) :
    (subLineSeedDist i).IsProbability := by
  solve_by_elim [Distribution.restrict_isProbability]

/-- The auxiliary randomness law of the sampling procedure: the extended
coordinate is uniform, the extended point and direction are uniform and
independent of it, and the two seeds are independent and uniform on the
coordinate-index fibers of the two coordinates carried by the two source
lines.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineSamplingDist (P : AdmissibleParams) :
    Distribution (Fin (2 * P.m + 2) × SubLineSamplingData P) :=
  Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
    (Distribution.prod (uniformDistribution (SubLinePointDir P))
        (Distribution.prod (subLineSeedDist (subLineXIndex k))
          (subLineSeedDist (subLineZIndex k)))).map fun w => (k, w)

/-- The auxiliary randomness law has total mass one. -/
theorem subLineSamplingDist_isProbability (P : AdmissibleParams) :
    (subLineSamplingDist P).IsProbability := by
  refine Distribution.bind_isProbability _ _
    (uniformDistribution_isProbability _) fun k _ => ?_
  exact Distribution.IsProbability.map
    (Distribution.prod_isProbability (μ := _) (ν := _) (uniformDistribution_isProbability _)
      (Distribution.prod_isProbability (μ := _) (ν := _) (subLineSeedDist_isProbability P _)
        (subLineSeedDist_isProbability P _))) _

/-! ## The sampled triple -/

section

variable (P : AdmissibleParams) (kind : LineKind)

/-- The extended line of a branch: the canonical axis or diagonal line of an
extended sample.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineExtLineOfSample (s : DirectLdSpace P.extendedDirectLd) :
    DirectLineDesc P.extendedDirectLd :=
  match kind with
  | .axis => directALineDescOf P.extendedDirectLd s
  | .diagonal => directDLineDescOf P.extendedDirectLd s

/-- The extended line of a branch, read off the auxiliary randomness.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineExtLine
    (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P) :
    DirectLineDesc P.extendedDirectLd :=
  subLineExtLineOfSample P kind ⟨w.1.1, k, w.1.2⟩

/-- A source line of a branch: the canonical axis or diagonal line decoded
from a point block, a scalar seed and a direction block.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineSourceLine
    (b : PauliPoint P) (s : ScalarQ P.toLdParams)
    (d : PauliPoint P) : LineDesc P.toLdParams :=
  match kind with
  | .axis => aLineDescOfBlock P.toLdParams (b, (s, d))
  | .diagonal => dLineDescOfBlock P.toLdParams (b, (s, d))

variable {P} in
/-- The triple sampled by one branch of the procedure: the extended line
together with the two source lines decoded from its two coordinate blocks and
from the two scalar seeds.  Blueprint `lem:qld-sublines`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
-/
noncomputable def subLineTripleOf
    (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P) : SubLineTriple P :=
  (subLineExtLine P kind k w,
    (subLineSourceLine P kind (projX (directPointToPauli w.1.1)) w.2.1
        (projX (directPointToPauli w.1.2)),
      subLineSourceLine P kind (projZ (directPointToPauli w.1.1)) w.2.2
        (projZ (directPointToPauli w.1.2))))

/-- The law of the triples sampled by one branch.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineBranchDist :
    Distribution (SubLineTriple P) :=
  (subLineSamplingDist P).map fun w => subLineTripleOf kind w.1 w.2

end

/-- The sub-line law of `lem:qld-sublines`: the equal mixture of the two
branches of the sampling procedure.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineDist (P : AdmissibleParams) :
    Distribution (SubLineTriple P) :=
  Distribution.bind (uniformDistribution (Fin 2))
    ![subLineBranchDist P .axis, subLineBranchDist P .diagonal]

/-! ## Elementary evaluations of the sampled triple -/

section

variable (P : AdmissibleParams) (kind : LineKind)

section

variable (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P)

/-- The direction of the extended line of a branch is the branch direction. -/
theorem subLineExtLine_direction :
    (subLineExtLine P kind k w).direction =
      subLineExtDirection kind k w.1.2 := by
  cases kind <;> rfl

/-- The base of the extended line of a branch is the canonical representative
of the drawn point in the branch direction. -/
theorem subLineExtLine_base :
    (subLineExtLine P kind k w).base =
      lineRepMap (subLineExtDirection kind k w.1.2) w.1.1 := by
  cases kind <;> rfl

end

section

variable (b : PauliPoint P) (s : ScalarQ P.toLdParams) (d : PauliPoint P)

/-- The direction of a source line of a branch is the branch source direction
at the coordinate index named by its seed. -/
theorem subLineSourceLine_direction :
    (subLineSourceLine P kind b s d).direction =
      subLineSourceDirection kind (chiIndex P.toLdParams s) d := by
  cases kind <;> rfl

/-- The base of a source line of a branch is the canonical representative of
its point block in its own direction. -/
theorem subLineSourceLine_base :
    (subLineSourceLine P kind b s d).base =
      lineRepMap (subLineSourceDirection kind (chiIndex P.toLdParams s) d)
        b := by
  cases kind <;> rfl

end

end

/-! ## The support of the sub-line law -/

/-- Every triple in the support of the sub-line law is sampled by one branch
from auxiliary randomness whose two seeds lie in the coordinate-index fibers
of the two coordinates carried by the two source lines.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem exists_samplingData_of_mem_subLineDist_support {P : AdmissibleParams}
    {sample : SubLineTriple P} (hsample : sample ∈ (subLineDist P).support) :
    ∃ (kind : LineKind) (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P),
      chiIndex P.toLdParams w.2.1 = subLineXIndex k ∧
        chiIndex P.toLdParams w.2.2 = subLineZIndex k ∧
        sample = subLineTripleOf kind k w := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hsample
  obtain ⟨kind, hkind⟩ : ∃ kind : LineKind,
      sample ∈ (subLineBranchDist P kind).support := by
    fin_cases c
    · exact Exists.intro LineKind.axis hc
    · exact Exists.intro LineKind.diagonal hc
  obtain ⟨kw, hkw, hkw'⟩ := Finset.mem_image.mp hkind
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp
    (hkw)
  obtain ⟨w, hw, hw'⟩ := Finset.mem_image.mp hk
  obtain ⟨-, hseeds⟩ := Finset.mem_product.mp hw
  obtain ⟨hsx, hsz⟩ := Finset.mem_product.mp hseeds
  refine ⟨kind, k, w, ((Finset.mem_filter.mp hsx).2), ((Finset.mem_filter.mp hsz).2), ?_⟩
  rw [← hkw', ← hw']

/-! ## Pointwise properties of a sampled triple -/

/-- The direction of the source `X` line of a sampled triple is the branch
source direction at the coordinate carried by that line. -/
theorem subLineTripleOf_xDirection {P : AdmissibleParams} (kind : LineKind)
    {k : Fin (2 * P.m + 2)} {w : SubLineSamplingData P}
    (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex k) :
    (subLineTripleOf kind k w).2.1.direction =
      subLineSourceDirection kind (subLineXIndex k)
        (projX (directPointToPauli w.1.2)) := by
  have h : (subLineTripleOf kind k w).2.1.direction =
      _ :=
    subLineSourceLine_direction P kind _ w.2.1 _
  simp_all

/-- The direction of the source `Z` line of a sampled triple is the branch
source direction at the coordinate carried by that line. -/
theorem subLineTripleOf_zDirection {P : AdmissibleParams} (kind : LineKind)
    {k : Fin (2 * P.m + 2)} {w : SubLineSamplingData P}
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex k) :
    (subLineTripleOf kind k w).2.2.direction =
      subLineSourceDirection kind (subLineZIndex k)
        (projZ (directPointToPauli w.1.2)) := by
  have h : (subLineTripleOf kind k w).2.2.direction =
      _ :=
    subLineSourceLine_direction P kind _ w.2.2 _
  simp_all

/-- The `X` block of the direction of the extended line of a sampled triple
lies in the line spanned by the direction of its source `X` line. -/
theorem subLineTripleOf_xSpan {P : AdmissibleParams} (kind : LineKind)
    {k : Fin (2 * P.m + 2)} {w : SubLineSamplingData P}
    (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex k) :
    projX (directPointToPauli (subLineTripleOf kind k w).1.direction) ∈
      Submodule.span (PauliScalar P)
        ({(subLineTripleOf kind k w).2.1.direction} :
          Set (PauliPoint P)) := by
  have hext : (subLineTripleOf kind k w).1.direction =
      _ := subLineExtLine_direction P kind k w
  rw [subLineTripleOf_xDirection kind hx, hext]
  apply projX_subLineExtDirection_mem_span

/-- The `Z` block of the direction of the extended line of a sampled triple
lies in the line spanned by the direction of its source `Z` line. -/
theorem subLineTripleOf_zSpan {P : AdmissibleParams} (kind : LineKind)
    {k : Fin (2 * P.m + 2)} {w : SubLineSamplingData P}
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex k) :
    projZ (directPointToPauli (subLineTripleOf kind k w).1.direction) ∈
      Submodule.span (PauliScalar P)
        ({(subLineTripleOf kind k w).2.2.direction} :
          Set (PauliPoint P)) := by
  have hext : (subLineTripleOf kind k w).1.direction =
      _ := subLineExtLine_direction P kind k w
  rw [subLineTripleOf_zDirection kind hz, hext]
  apply projZ_subLineExtDirection_mem_span

/-- The base of the source `X` line of a sampled triple is the canonical
representative, in its own direction, of the `X` block of the base of the
extended line.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_xBase {P : AdmissibleParams} (kind : LineKind)
    {k : Fin (2 * P.m + 2)} {w : SubLineSamplingData P}
    (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex k) :
    (subLineTripleOf kind k w).2.1.base =
      lineRepMap (subLineTripleOf kind k w).2.1.direction
        (projX (directPointToPauli (subLineTripleOf kind k w).1.base)) := by
  have hbase : (subLineTripleOf kind k w).2.1.base =
      lineRepMap (subLineSourceDirection kind (subLineXIndex k)
        (projX (directPointToPauli w.1.2)))
        (projX (directPointToPauli w.1.1)) := by
    have h : (subLineTripleOf kind k w).2.1.base =
        _ :=
      subLineSourceLine_base P kind _ w.2.1 _
    simp_all
  have hextbase : (subLineTripleOf kind k w).1.base =
      _ :=
    subLineExtLine_base P kind k w
  rw [hbase, subLineTripleOf_xDirection kind hx, hextbase]
  exact (lineRepMap_projX_directPointToPauli_lineRepMap P w.1.1
    (projX_subLineExtDirection_mem_span P kind k w.1.2)).symm

/-- The base of the source `Z` line of a sampled triple is the canonical
representative, in its own direction, of the `Z` block of the base of the
extended line.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_zBase {P : AdmissibleParams} (kind : LineKind)
    {k : Fin (2 * P.m + 2)} {w : SubLineSamplingData P}
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex k) :
    (subLineTripleOf kind k w).2.2.base =
      lineRepMap (subLineTripleOf kind k w).2.2.direction
        (projZ (directPointToPauli (subLineTripleOf kind k w).1.base)) := by
  have hbase : (subLineTripleOf kind k w).2.2.base =
      lineRepMap (subLineSourceDirection kind (subLineZIndex k)
        (projZ (directPointToPauli w.1.2)))
        (projZ (directPointToPauli w.1.1)) := by
    have h : (subLineTripleOf kind k w).2.2.base =
        _ :=
      subLineSourceLine_base P kind _ w.2.2 _
    simp_all
  have hextbase : (subLineTripleOf kind k w).1.base =
      _ :=
    subLineExtLine_base P kind k w
  rw [hbase, subLineTripleOf_zDirection kind hz, hextbase]
  exact (lineRepMap_projZ_directPointToPauli_lineRepMap P w.1.1
    (projZ_subLineExtDirection_mem_span P kind k w.1.2)).symm

/-- Every sampled triple carries affine data sufficient for
`combineLinePoly_spec`.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_compatibility (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P)
    (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex k)
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex k) :
    ∃ aX bX aZ bZ uAlpha vAlpha uBeta vBeta : PauliScalar P,
      IsCombineLineCompatible
        (directPointToPauli (subLineTripleOf kind k w).1.base)
        (directPointToPauli (subLineTripleOf kind k w).1.direction)
        (subLineTripleOf kind k w).2.1.base
        (subLineTripleOf kind k w).2.1.direction
        (subLineTripleOf kind k w).2.2.base
        (subLineTripleOf kind k w).2.2.direction
        aX bX aZ bZ uAlpha vAlpha uBeta vBeta := by
  obtain ⟨aX, haX⟩ := Submodule.mem_span_singleton.mp
    (sub_lineRepMap_mem_span (subLineTripleOf kind k w).2.1.direction
      _)
  obtain ⟨aZ, haZ⟩ := Submodule.mem_span_singleton.mp
    (sub_lineRepMap_mem_span (subLineTripleOf kind k w).2.2.direction
      _)
  obtain ⟨bX, hbX⟩ := Submodule.mem_span_singleton.mp
    (subLineTripleOf_xSpan kind hx)
  obtain ⟨bZ, hbZ⟩ := Submodule.mem_span_singleton.mp
    (subLineTripleOf_zSpan kind hz)
  have hcompat := isCombineLineCompatible_of_blocks
    _
    _
    (subLineTripleOf kind k w).2.1.base
    _
    (subLineTripleOf kind k w).2.2.base
    _
    aX bX aZ bZ (by
      rw [subLineTripleOf_xBase kind hx, haX]
      abel) hbX.symm (by
      rw [subLineTripleOf_zBase kind hz, haZ]
      abel) hbZ.symm
  exact ⟨aX, bX, aZ, bZ, _, _, _, _, hcompat⟩

/-! ## Total mass and extended marginal -/

/-- The index-first decomposition of an extended direct sample, read at the
bare extended dimension.  This is the decomposition
`directLdSpaceIndexEquiv` of `def:ld-question-distribution` with its stored
coordinate typed by the bare dimension `2 m + 2`. -/
private def subLineSampleEquiv (P : AdmissibleParams) :
    DirectLdSpace P.extendedDirectLd ≃
      Fin (2 * P.m + 2) × SubLinePointDir P where
  toFun s := (s.index, s.point, s.direction)
  invFun w := ⟨w.2.1, w.1, w.2.2⟩
  left_inv s := by cases s; rfl
  right_inv w := by cases w; rfl

/-- The extended-line marginal of one branch of the sub-line law is the law of
the canonical line of the corresponding kind through a uniformly sampled
extended direct sample.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_fst (P : AdmissibleParams) (kind : LineKind) :
    (subLineBranchDist P kind).map Prod.fst =
      (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map
        (subLineExtLineOfSample P kind) := by
  let dist := uniformDistribution (Fin (2 * P.m + 2))
  classical
  have hstep1 : (subLineBranchDist P kind).map Prod.fst =
      Distribution.bind dist fun k =>
        (Distribution.prod (uniformDistribution (SubLinePointDir P))
            (Distribution.prod (subLineSeedDist (subLineXIndex k))
              (subLineSeedDist (subLineZIndex k)))).map
          fun w => subLineExtLineOfSample P kind ⟨w.1.1, k, w.1.2⟩ := by
    rw [subLineBranchDist, Distribution.map_map, subLineSamplingDist,
      Distribution.bind_map]
    refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
    rw [Distribution.map_map]
    rfl
  have hstep2 : ∀ k : Fin (2 * P.m + 2),
      (Distribution.prod (uniformDistribution (SubLinePointDir P))
          (Distribution.prod (subLineSeedDist (subLineXIndex k))
            (subLineSeedDist (subLineZIndex k)))).map
        (fun w => subLineExtLineOfSample P kind ⟨w.1.1, k, w.1.2⟩) =
      (uniformDistribution (SubLinePointDir P)).map
        (fun pd => subLineExtLineOfSample P kind ⟨pd.1, k, pd.2⟩) := by
    intro k
    rw [← Distribution.map_map (Distribution.prod (uniformDistribution (SubLinePointDir P)) (Distribution.prod (subLineSeedDist (subLineXIndex k)) (subLineSeedDist (subLineZIndex k)))) Prod.fst (fun pd => subLineExtLineOfSample P kind ⟨pd.1, k, pd.2⟩),
      Distribution.prod_map_fst (uniformDistribution (SubLinePointDir P)) (Distribution.prod_isProbability (subLineSeedDist_isProbability P (subLineXIndex k)) (subLineSeedDist_isProbability P (subLineZIndex k)))]
  have hstep3 :
      Distribution.bind dist (fun k =>
        (uniformDistribution (SubLinePointDir P)).map
          (fun pd => subLineExtLineOfSample P kind ⟨pd.1, k, pd.2⟩)) =
      (uniformDistribution (Fin (2 * P.m + 2) × SubLinePointDir P)).map
        (fun w => subLineExtLineOfSample P kind ⟨w.2.1, w.1, w.2.2⟩) := by
    rw [uniformDistribution_prod (Fin (2 * P.m + 2)) (SubLinePointDir P)]
    exact (Distribution.prod_map_eq_bind
      dist
      (uniformDistribution (SubLinePointDir P))
      (fun w => subLineExtLineOfSample P kind ⟨w.2.1, w.1, w.2.2⟩)).symm
  have hstep4 :
      (uniformDistribution (Fin (2 * P.m + 2) × SubLinePointDir P)).map
        (fun w => subLineExtLineOfSample P kind ⟨w.2.1, w.1, w.2.2⟩) =
      (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map
        (subLineExtLineOfSample P kind) := by
    rw [← uniformDistribution_map_equiv (subLineSampleEquiv P),
      Distribution.map_map]
    rfl
  simp_all

end

end MIPStarRE.QPBT
