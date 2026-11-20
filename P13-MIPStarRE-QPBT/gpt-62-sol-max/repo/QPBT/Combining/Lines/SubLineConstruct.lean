module

public import QPBT.Combining.Lines.SubLineBranch

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
noncomputable def subLineSeedDist (P : AdmissibleParams) (i : Fin P.m) :
    Distribution (ScalarQ P.toLdParams) :=
  ldSeedFiberDist P.toLdParams i

theorem subLineSeedDist_index {P : AdmissibleParams} {i : Fin P.m}
    {s : ScalarQ P.toLdParams} (hs : s ∈ (subLineSeedDist P i).support) :
    chiIndex P.toLdParams s = i := by
  simp only [subLineSeedDist, ldSeedFiberDist, Distribution.map_support] at hs
  obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hs
  exact chiIndex_seedOfIndexResidue P.toLdParams i r

section

variable (P : AdmissibleParams)
include P

/-- Every seed law of a source line has total mass one. -/
theorem subLineSeedDist_isProbability (i : Fin P.m) :
    (subLineSeedDist P i).IsProbability :=
  ldSeedFiberDist_isProbability P.toLdParams i

/-- The independent seeds for the two source blocks. -/
noncomputable def subLineSeedsDist (k : Fin (2 * P.m + 2)) :
    Distribution (ScalarQ P.toLdParams × ScalarQ P.toLdParams) :=
  Distribution.prod (subLineSeedDist P (subLineXIndex P k)) (subLineSeedDist P (subLineZIndex P k))

private theorem subLineSeedsDist_isProbability (k : Fin (2 * P.m + 2)) :
    (subLineSeedsDist P k).IsProbability :=
  Distribution.prod_isProbability _ _ (subLineSeedDist_isProbability P _) (subLineSeedDist_isProbability P _)

/-- Point, direction, and the two seed fibers at the stored index. -/
noncomputable def subLineBlocksDist (k : Fin (2 * P.m + 2)) :
    Distribution (SubLineSamplingData P) :=
  Distribution.prod (uniformDistribution (SubLinePointDir P))
    (subLineSeedsDist P k)

/-- The auxiliary randomness law of the sampling procedure: the extended
coordinate is uniform, the extended point and direction are uniform and
independent of it, and the two seeds are independent and uniform on the
coordinate-index fibers of the two coordinates carried by the two source
lines.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineSamplingDist :
    Distribution (Fin (2 * P.m + 2) × SubLineSamplingData P) :=
  Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
    (subLineBlocksDist P k).map fun w => (k, w)

/-- The auxiliary randomness law has total mass one. -/
theorem subLineSamplingDist_isProbability :
    (subLineSamplingDist P).IsProbability := by
  exact Distribution.bind_isProbability _ _ (uniformDistribution_isProbability _) fun k _ =>
    (Distribution.prod_isProbability _ _ (uniformDistribution_isProbability _)
      (subLineSeedsDist_isProbability P k)).map _

end

/-! ## The sampled triple -/

section

variable (P : AdmissibleParams)
include P

/-- The extended line of a branch: the canonical axis or diagonal line of an
extended sample.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineExtLineOfSample
    (kind : LineKind) (s : DirectLdSpace P.extendedDirectLd) :
    DirectLineDesc P.extendedDirectLd :=
  match kind with
  | .axis => directALineDescOf P.extendedDirectLd s
  | .diagonal => directDLineDescOf P.extendedDirectLd s

section

variable (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P)

/-- The extended line of a branch, read off the auxiliary randomness.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineExtLine :
    DirectLineDesc P.extendedDirectLd :=
  subLineExtLineOfSample P kind ⟨w.1.1, k, w.1.2⟩

/-- A source line of a branch: the canonical axis or diagonal line decoded
from a point block, a scalar seed and a direction block.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineSourceLine (kind : LineKind)
    (b : PauliPoint P) (s : ScalarQ P.toLdParams)
    (d : PauliPoint P) : LineDesc P.toLdParams :=
  match kind with
  | .axis => aLineDescOfBlock P.toLdParams (b, (s, d))
  | .diagonal => dLineDescOfBlock P.toLdParams (b, (s, d))

/-- Read the source line from its coordinate block and seed. -/
noncomputable def subLineSourceOf (W : PauliKind)
    (kind : LineKind) (w : SubLineSamplingData P) : LineDesc P.toLdParams :=
  subLineSourceLine P kind (subLineProject P W w.1.1) (W.component w.2) (subLineProject P W w.1.2)

/-- One extended line and its two source lines. -/
noncomputable def subLineTripleOf : SubLineTriple P :=
  (subLineExtLine P kind k w, subLineSourceOf P .X kind w, subLineSourceOf P .Z kind w)

end

/-- The law of the triples sampled by one branch.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineBranchDist (kind : LineKind) :
    Distribution (SubLineTriple P) :=
  (subLineSamplingDist P).map fun w => subLineTripleOf P kind w.1 w.2

/-- The sub-line law of `lem:qld-sublines`: the equal mixture of the two
branches of the sampling procedure.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineDist :
    Distribution (SubLineTriple P) :=
  Distribution.bind (uniformDistribution (Fin 2))
    ![subLineBranchDist P .axis, subLineBranchDist P .diagonal]

end

/-! ## Elementary evaluations of the sampled triple -/

section

variable (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P)
include P kind k w

/-- The extended line of a branch has the kind of that branch. -/
theorem subLineExtLine_kind :
    (subLineExtLine P kind k w).kind = kind := by
  cases kind <;> rfl

/-- The direction of the extended line of a branch is the branch direction. -/
theorem subLineExtLine_direction :
    (subLineExtLine P kind k w).direction =
      subLineExtDirection P kind k w.1.2 := by
  cases kind <;> rfl

/-- The base of the extended line of a branch is the canonical representative
of the drawn point in the branch direction. -/
theorem subLineExtLine_base :
    (subLineExtLine P kind k w).base =
      lineRepMap (subLineExtDirection P kind k w.1.2) w.1.1 := by
  cases kind <;> rfl

end

section

variable (P : AdmissibleParams) (kind : LineKind)
    (b : PauliPoint P) (s : ScalarQ P.toLdParams)
    (d : PauliPoint P)
include P kind b s d

/-- A source line of a branch has the kind of that branch. -/
theorem subLineSourceLine_kind :
    (subLineSourceLine P kind b s d).kind = kind := by
  cases kind <;> rfl

/-- The direction of a source line of a branch is the branch source direction
at the coordinate index named by its seed. -/
theorem subLineSourceLine_direction :
    (subLineSourceLine P kind b s d).direction =
      subLineSourceDirection P kind (chiIndex P.toLdParams s) d := by
  cases kind <;> rfl

/-- The base of a source line of a branch is the canonical representative of
its point block in its own direction. -/
theorem subLineSourceLine_base :
    (subLineSourceLine P kind b s d).base =
      lineRepMap (subLineSourceDirection P kind (chiIndex P.toLdParams s) d)
        b := by
  cases kind <;> rfl

end

/-! ## The support of the sub-line law -/

/-- Every triple in the support of the sub-line law is sampled by one branch
from auxiliary randomness whose two seeds lie in the coordinate-index fibers
of the two coordinates carried by the two source lines.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem exists_samplingData_of_mem_subLineDist_support (P : AdmissibleParams)
    {sample : SubLineTriple P} (hsample : sample ∈ (subLineDist P).support) :
    ∃ (kind : LineKind) (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P),
      chiIndex P.toLdParams w.2.1 = subLineXIndex P k ∧
        chiIndex P.toLdParams w.2.2 = subLineZIndex P k ∧
        sample = subLineTripleOf P kind k w := by
  classical
  have hbind := hsample
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hbind
  obtain ⟨kind, hkind⟩ : ∃ kind : LineKind,
      sample ∈ (subLineBranchDist P kind).support := by
    fin_cases c
    · exact ⟨.axis, by simpa using hc⟩
    · exact ⟨.diagonal, by simpa using hc⟩
  obtain ⟨kw, hkw, hkw'⟩ := Finset.mem_image.mp hkind
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp
    (show kw ∈ (uniformDistribution (Fin (2 * P.m + 2))).support.biUnion
      (fun k => ((subLineBlocksDist P k).map
        (fun w => (k, w))).support) from hkw)
  obtain ⟨w, hw, hw'⟩ := Finset.mem_image.mp hk
  obtain ⟨-, hseeds⟩ := Finset.mem_product.mp hw
  obtain ⟨hsx, hsz⟩ := Finset.mem_product.mp hseeds
  refine ⟨kind, k, w, subLineSeedDist_index hsx, subLineSeedDist_index hsz, ?_⟩
  rw [← hkw', ← hw']

/-! ## Pointwise properties of a sampled triple -/

section

variable (P : AdmissibleParams) (W : PauliKind)
    (kind : LineKind) (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P)
    (hs : chiIndex P.toLdParams (W.component w.2) = subLineIndex P W k)
include P W kind k w hs

/-- The affine parameter on an extended line projects to an affine parameter
on either source line. -/
private theorem subLineSourceOf_parameters :
    let line := subLineSourceOf P W kind w
    ∃ a b : PauliScalar P,
      subLineProject P W (subLineExtLine P kind k w).base = line.base + a • line.direction ∧
      subLineProject P W (subLineExtLine P kind k w).direction = b • line.direction := by
  dsimp only
  have hd : (subLineSourceOf P W kind w).direction =
      subLineSourceDirection P kind (subLineIndex P W k) (subLineProject P W w.1.2) := by
    rw [subLineSourceOf, subLineSourceLine_direction, hs]
  have hb : (subLineSourceOf P W kind w).base =
      lineRepMap (subLineSourceOf P W kind w).direction (subLineProject P W w.1.1) := by
    rw [subLineSourceOf, subLineSourceLine_base, subLineSourceLine_direction]
  have hrep := subLineProject_representative P W kind k w.1.1 w.1.2 0
  simp only [zero_smul, add_zero] at hrep
  rw [subLineExtLine_base, subLineExtLine_direction, hb, hd, ← hrep]
  obtain ⟨a, ha⟩ := mem_linePoints_lineRepMap
    (subLineSourceDirection P kind (subLineIndex P W k) (subLineProject P W w.1.2))
    (subLineProject P W (lineRepMap (subLineExtDirection P kind k w.1.2) w.1.1))
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (subLineProject_direction_mem_span P W kind k w.1.2)
  exact ⟨a, b, ha, hb.symm⟩

private theorem subLineSourceOf_incidence
    {u : DirectPoint P.extendedDirectLd}
    (hu : u ∈ (subLineExtLine P kind k w).pointSet) :
    subLineProject P W u ∈ (subLineSourceOf P W kind w).pointSet := by
  obtain ⟨a, b, ha, hb⟩ := subLineSourceOf_parameters P W kind k w hs
  obtain ⟨t, rfl⟩ := hu
  refine ⟨a + extendedDirectScalarEquiv P t * b, ?_⟩
  rw [subLineProject_affine, ha, hb, smul_smul, add_smul, add_assoc]

end

section

variable (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2)) (w : SubLineSamplingData P)
include P kind k w

section

variable (hx : chiIndex P.toLdParams w.2.1 = subLineXIndex P k)
    (hz : chiIndex P.toLdParams w.2.2 = subLineZIndex P k)
include hx hz

/-- Every point of the sampled extended line projects onto both source lines. -/
theorem subLineTripleOf_incidence
    {u : DirectPoint P.extendedDirectLd}
    (hu : u ∈ (subLineTripleOf P kind k w).1.pointSet) :
    projX (directPointToPauli P u) ∈ (subLineTripleOf P kind k w).2.1.pointSet ∧
    projZ (directPointToPauli P u) ∈ (subLineTripleOf P kind k w).2.2.pointSet :=
  ⟨subLineSourceOf_incidence P .X kind k w hx hu, subLineSourceOf_incidence P .Z kind k w hz hu⟩

/-- Every sampled triple carries affine data sufficient for
`combineLinePoly_spec`.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_compatibility :
    ∃ aX bX aZ bZ uAlpha vAlpha uBeta vBeta : PauliScalar P,
      IsCombineLineCompatible
        (directPointToPauli P (subLineTripleOf P kind k w).1.base)
        (directPointToPauli P (subLineTripleOf P kind k w).1.direction)
        (subLineTripleOf P kind k w).2.1.base
        (subLineTripleOf P kind k w).2.1.direction
        (subLineTripleOf P kind k w).2.2.base
        (subLineTripleOf P kind k w).2.2.direction
        aX bX aZ bZ uAlpha vAlpha uBeta vBeta := by
  obtain ⟨aX, bX, haX, hbX⟩ := subLineSourceOf_parameters P .X kind k w hx
  obtain ⟨aZ, bZ, haZ, hbZ⟩ := subLineSourceOf_parameters P .Z kind k w hz
  exact ⟨aX, bX, aZ, bZ, _, _, _, _,
    isCombineLineCompatible_of_blocks _ _ _ _ _ _ _ _ _ _ haX hbX haZ hbZ⟩

end

/-- An extended axis line of a sampled triple has axis-parallel source lines.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_axis_closure
    (haxis : (subLineTripleOf P kind k w).1.kind = .axis) :
    (subLineTripleOf P kind k w).2.1.kind = .axis ∧
      (subLineTripleOf P kind k w).2.2.kind = .axis := by
  have hkind : kind = .axis := by
    have h :=
      subLineExtLine_kind P kind k w
    rw [← h]
    exact haxis
  subst hkind
  exact ⟨subLineSourceLine_kind P .axis _ _ _,
    subLineSourceLine_kind P .axis _ _ _⟩

end

/-! ## Total mass and extended marginal -/

section

variable (P : AdmissibleParams)
include P

/-- The sub-line law has total mass one. -/
theorem subLineDist_isProbability :
    (subLineDist P).IsProbability := by
  refine Distribution.bind_isProbability _ _
    (uniformDistribution_isProbability _) fun c _ => ?_
  fin_cases c <;> exact (subLineSamplingDist_isProbability P).map _

/-- The extended-line marginal of one branch of the sub-line law is the law of
the canonical line of the corresponding kind through a uniformly sampled
extended direct sample.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_fst (kind : LineKind) :
    (subLineBranchDist P kind).map Prod.fst =
      (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map
        (subLineExtLineOfSample P kind) := by
  classical
  let e : DirectLdSpace P.extendedDirectLd ≃ Fin (2 * P.m + 2) × SubLinePointDir P :=
    directLdSpaceIndexEquiv _
  let read (w : Fin (2 * P.m + 2) × SubLinePointDir P) :=
    subLineExtLineOfSample P kind (e.symm w)
  calc
    _ = (uniformDistribution (Fin (2 * P.m + 2) × SubLinePointDir P)).map read := by
      rw [subLineBranchDist, Distribution.map_map, subLineSamplingDist, Distribution.bind_map,
        uniformDistribution_prod, Distribution.prod_map_eq_bind]
      refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
      rw [Distribution.map_map]
      exact Distribution.prod_map_of_fst _ _ (subLineSeedsDist_isProbability P k)
        (fun pd => read (k, pd))
    _ = _ := by
      rw [← uniformDistribution_map_equiv e, Distribution.map_map]
      simp [read]

/-- The extended-line marginal of the sub-line law is the extended-line
marginal of the directly indexed line-point law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_map_fst :
    (subLineDist P).map Prod.fst =
      (directLinePointDist P.extendedDirectLd).map Prod.fst := by
  classical
  rw [subLineDist, Distribution.bind_map, directLinePointDist,
    ← Distribution.bind_uniform_fin_two, Distribution.bind_map]
  refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · change (subLineBranchDist P .axis).map _ = (directALinePointDist _).map _
    rw [subLineBranchDist_map_fst, directALinePointDist, Distribution.map_map]
    rfl
  · change (subLineBranchDist P .diagonal).map _ = (directDLinePointDist _).map _
    rw [subLineBranchDist_map_fst, directDLinePointDist, Distribution.map_map]
    rfl

end

end

end MIPStarRE.QPBT
