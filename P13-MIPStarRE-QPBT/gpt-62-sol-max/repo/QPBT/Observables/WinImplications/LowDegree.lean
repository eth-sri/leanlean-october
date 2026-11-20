module

public import QPBT.Observables.WinImplications.Averages

/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

local instance linePointFintypeCanonical (P : AdmissibleParams) :
    Fintype (LinePointSample P.toLdParams) :=
  linePointFintype P

/-- Coordinates outside one low-degree register in the Pauli seed. -/
abbrev PauliLdRemainder (P : AdmissibleParams) :=
  (PauliPoint P) × PauliScalar P × PauliScalar P

/-- Split a Pauli seed into a basis-selected low-degree seed and unused coordinates. -/
private def pauliLdSplit (P : AdmissibleParams) (W : PauliKind) :
    PauliSpace P ≃ LdSpace P.toLdParams × PauliLdRemainder P where
  toFun z :=
    (pauliToLd P W z,
      (match W with | .X => pauliZBlock z | .Z => pauliXBlock z,
        pauliRXBlock z, pauliRZBlock z))
  invFun zr := fun i =>
    match i with
    | .inl (.inl (.inl (.inl (.inl j)))) =>
        match W with
        | .X => zr.1 (.inl (.inl j))
        | .Z => zr.2.1 j
    | .inl (.inl (.inl (.inl (.inr j)))) =>
        match W with
        | .X => zr.2.1 j
        | .Z => zr.1 (.inl (.inl j))
    | .inl (.inl (.inl (.inr _))) => zr.1 (.inl (.inr ()))
    | .inl (.inl (.inr j)) => zr.1 (.inr j)
    | .inl (.inr _) => zr.2.2.1
    | .inr _ => zr.2.2.2
  left_inv z := by
    funext i
    rcases i with ((((j | j) | u) | j) | u) | u <;> cases W <;> rfl
  right_inv zr := by
    rcases zr with ⟨z, other, rX, rZ⟩
    apply Prod.ext
    · funext i
      rcases i with (j | u) | j <;> cases W <;> rfl
    · cases W <;> rfl

/-- Coordinates discarded by the shared Pair and Magic Square projection. -/
abbrev PauliSharedRemainder (P : AdmissibleParams) :=
  PauliScalar P × (PauliPoint P)

/-- Split a Pauli seed into its shared tuple and discarded scalar/direction blocks. -/
def pauliSharedSplit (P : AdmissibleParams) :
    PauliSpace P ≃ PauliTuple P × PauliSharedRemainder P where
  toFun z :=
    ((pauliXBlock z, pauliZBlock z, pauliRXBlock z, pauliRZBlock z),
      pauliScalarBlock z, pauliDirectionBlock z)
  invFun zr := fun i =>
    match i with
    | .inl (.inl (.inl (.inl (.inl j)))) => zr.1.1 j
    | .inl (.inl (.inl (.inl (.inr j)))) => zr.1.2.1 j
    | .inl (.inl (.inl (.inr _))) => zr.2.1
    | .inl (.inl (.inr j)) => zr.2.2 j
    | .inl (.inr _) => zr.1.2.2.1
    | .inr _ => zr.1.2.2.2
  left_inv z := by
    funext i
    rcases i with ((((j | j) | u) | j) | u) | u <;> rfl
  right_inv zr := by rfl

@[simp] theorem pauliSharedSplit_apply (P : AdmissibleParams) (z : PauliSpace P) :
    pauliSharedSplit P z =
      ((pauliXBlock z, pauliZBlock z, pauliRXBlock z, pauliRZBlock z),
        pauliScalarBlock z, pauliDirectionBlock z) := rfl

/-- Split a low-degree seed into its point and unused scalar/direction blocks. -/
private def ldPointSplit (L : LdParams) :
    LdSpace L ≃ (LdPoint L) × (ScalarQ L × (LdPoint L)) where
  toFun z := (z.point, z.seed, z.direction)
  invFun zr := fun i =>
    match i with
    | .inl (.inl j) => zr.1 j
    | .inl (.inr _) => zr.2.1
    | .inr j => zr.2.2 j
  left_inv z := by
    funext i
    rcases i with (j | u) | j <;> rfl
  right_inv zr := by rfl

/-- Uniform Pauli seeds have the uniform low-degree marginal in either basis. -/
theorem avgOver_pauliToLd_uniform (P : AdmissibleParams) (W : PauliKind)
    (f : LdSpace P.toLdParams → ℝ) :
    avgOver (uniformDistribution (PauliSpace P)) (fun z => f (pauliToLd P W z)) =
      avgOver (uniformDistribution (LdSpace P.toLdParams)) f := avgOver_uniform_equiv_fst (pauliLdSplit P W) f

/-- Uniform Pauli seeds have the uniform shared-tuple marginal. -/
theorem avgOver_pauliTuple_uniform (P : AdmissibleParams)
    (f : PauliTuple P → ℝ) :
    avgOver (uniformDistribution (PauliSpace P))
        (fun z => f (pauliSharedSplit P z).1) =
      avgOver (uniformDistribution (PauliTuple P)) f := avgOver_uniform_equiv_fst (pauliSharedSplit P) f

/-- The point block of a uniform low-degree seed is uniform. -/
theorem avgOver_ldPoint_uniform (L : LdParams)
    (f : (LdPoint L) → ℝ) :
    avgOver (uniformDistribution (LdSpace L)) (fun z => f z.point) =
      avgOver (uniformDistribution (LdPoint L)) f := avgOver_uniform_equiv_fst (ldPointSplit L) f

/-- The point conditioning map produces the typed point content. -/
theorem pauliCL_point_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliCL P (.point W) z =
      ProjectiveSetting.contentOfPoint P W (pauliToLd P W z).point := by rfl

/-- The shared conditioning map produces the typed tuple content. -/
theorem pauliCL_shared_eq (P : AdmissibleParams) (t : PauliType)
    (ht : pauliCL P t = pauliSharedProjection) (z : PauliSpace P) :
    pauliCL P t z = ProjectiveSetting.contentOfTuple P
      (pauliXBlock z) (pauliZBlock z) (pauliRXBlock z) (pauliRZBlock z) := by tauto

/-- Reading a typed point content recovers its point block. -/
theorem pauliPointBlock_contentOfPoint (P : AdmissibleParams)
    (W : PauliKind) (u : PauliPoint P) :
    pauliPointBlock W (ProjectiveSetting.contentOfPoint P W u) = u := by
  funext j
  cases W <;> rfl

section

variable (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
include P W line

/-- Reading a typed line content recovers its canonical base. -/
theorem pauliPointBlock_contentOfLine :
    pauliPointBlock W (ProjectiveSetting.contentOfLine P W line) = line.base := by
  funext j
  cases W <;> rfl

/-- Reading a typed line content recovers its seed. -/
theorem pauliScalarBlock_contentOfLine :
    pauliScalarBlock (ProjectiveSetting.contentOfLine P W line) = line.seed := by rfl

/-- Reading a typed line content recovers its geometric direction. -/
theorem pauliDirectionBlock_contentOfLine
    (hline : line.kind = .diagonal) :
    pauliDirectionBlock (ProjectiveSetting.contentOfLine P W line) = line.direction := by
  funext j
  cases line with
  | axis => simp [LineDesc.kind] at hline
  | diagonal => cases W <;> rfl

end

/-- Zero-padding a coefficient list does not change its polynomial value. -/
theorem evalCoefficient_padTo {L : LdParams} {c c' : ℕ} (h : c ≤ c')
    (f : DegPoly L c) (t : ScalarQ L) :
    evalCoefficient (DegPoly.padTo h f) t = evalCoefficient f t := by
  exact evalCoefficient_pad (Nat.succ_le_succ h) f t

/-- A uniquely determined line evaluation is returned by `evalOpt`. -/
theorem evalOpt_eq_some_of_evaluatesTo {L : LdParams} {c : ℕ}
    (line : LineDesc L) (f : DegPoly L c) (u : LdPoint L)
    (a : ScalarQ L) (h : EvaluatesTo line f u a) :
    evalOpt line u f = some a := by
  exact (evalOpt_eq_some_iff line u f a).mpr h

/-- The Pauli question tag for a line in the selected basis. -/
private abbrev lineTag (k : LineKind) (W : PauliKind) : PauliType :=
  match k with
  | .axis => .aline W
  | .diagonal => .dline W

private theorem pauliCL_sampledLine (P : AdmissibleParams) (k : LineKind)
    (W : PauliKind) (z : PauliSpace P) :
    pauliCL P (lineTag k W) z = ProjectiveSetting.contentOfLine P W
      (sampledLine P.toLdParams k (pauliToLd P W z)) := by
  cases k <;> apply congrArg (embedLd P W) <;> funext i <;>
    rcases i with (j | u) | j <;> rfl

/-- A successful line/point check has equal evaluation-class labels for either line kind. -/
private theorem sampledLineLabels_eq_of_win (P : AdmissibleParams) (k : LineKind)
    (W : PauliKind) (z : PauliSpace P) (A B : PauliAnswer P)
    (hwin : pauliWinPredicate P (lineTag k W, pauliCL P (lineTag k W) z)
      (.point W, pauliCL P (.point W) z) A B = true) :
    let raw := pauliToLd P W z
    let line := sampledLine P.toLdParams k raw
    evalOpt line raw.point (ProjectiveSetting.lineAnswerOrZero P line A) =
      some (ProjectiveSetting.pointAnswerOrZero B) := by
  have hmem : (pauliToLd P W z).point ∈
        (sampledLine P.toLdParams k (pauliToLd P W z)).pointSet := by
    cases k <;> exact mem_linePoints_lineRepMap _ _
  rw [pauliCL_sampledLine, pauliCL_point_eq] at hwin
  cases k <;> cases A <;> cases B <;>
    simp only [lineTag, pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  all_goals
    apply evalOpt_eq_some_of_evaluatesTo
    refine ⟨hmem, fun t ht => ?_⟩
    rename_i f a
  · change evalCoefficient (DegPoly.padTo (Nat.le_mul_of_pos_left P.d
      (Nat.zero_lt_of_lt P.one_le_m)) f) t = a
    rw [evalCoefficient_padTo]
    apply hwin t
    rw [pauliPointBlock_contentOfPoint, pauliPointBlock_contentOfLine,
      pauliScalarBlock_contentOfLine]
    exact ht
  · change evalCoefficient f t = a
    apply hwin t
    rw [pauliPointBlock_contentOfPoint, pauliPointBlock_contentOfLine,
      pauliDirectionBlock_contentOfLine _ _ _ rfl]
    exact ht

/-- The ordered line/point verifier edge. -/
private def linePointEdge (k : LineKind) (W : PauliKind) : PauliEdge :=
  ⟨(lineTag k W, .point W), by cases k <;> simp [lineTag, pauliEdges]⟩

/-- The point/Pauli verifier edge in one Pauli basis. -/
def pointPauliEdge (W : PauliKind) : PauliEdge :=
  ⟨(.point W, .pauli W), by simp [pauliEdges]⟩

/-- The Pair-W/Pair verifier edge in one Pauli basis. -/
def pairWPairEdge (W : PauliKind) : PauliEdge :=
  ⟨(.pairW W, .pair), by simp [pauliEdges]⟩

/-- The point/Pair-W verifier edge in one Pauli basis. -/
def pointPairWEdge (W : PauliKind) : PauliEdge :=
  ⟨(.point W, .pairW W), by simp [pauliEdges]⟩

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε)
include P ε S

/-- Source-answer mismatch mass for the completed line and point readouts. -/
noncomputable def lowDegreeMismatchMass (W : PauliKind)
    (sample : LinePointSample P.toLdParams) : ℝ :=
  outcomeEventWeight S.toStrategy
    (ProjectiveSetting.lineQuestion P W sample.1)
    (ProjectiveSetting.pointQuestion P W sample.2)
    (fun A B =>
      evalOpt sample.1 sample.2
          (ProjectiveSetting.lineAnswerOrZero P sample.1 A) ≠
        some (ProjectiveSetting.pointAnswerOrZero B))

private theorem lineMismatch_le_rejection (k : LineKind) (W : PauliKind) (z : PauliSpace P) :
    lowDegreeMismatchMass S W
        (sampledLine P.toLdParams k (pauliToLd P W z), (pauliToLd P W z).point) ≤
      pauliRejectionAt S.toStrategy (linePointEdge k W) z := by
  have hq : ProjectiveSetting.lineQuestion P W
      (sampledLine P.toLdParams k (pauliToLd P W z)) =
      (lineTag k W, pauliCL P (lineTag k W) z) := by
    rw [pauliCL_sampledLine]
    cases k <;> rfl
  unfold lowDegreeMismatchMass
  rw [hq, ProjectiveSetting.pointQuestion, ← pauliCL_point_eq]
  exact mismatch_le_pauliRejectionAt S.toStrategy (linePointEdge k W) z _ _
    (sampledLineLabels_eq_of_win P k W z)

/-- The completed low-degree consistency defect is its source-answer mismatch mass. -/
theorem lowDegreeConsistency_eq_mismatch (W : PauliKind) :
    bipartiteDefect (linePointDist P.toLdParams)
        (fun sample => S.lineEvalMeas .alice W sample.1 sample.2)
        (fun sample => S.pointMeasOption .bob W sample.2)
        S.toStrategy.ψ =
      avgOver (linePointDist P.toLdParams) (fun sample =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.lineQuestion P W sample.1)
          (ProjectiveSetting.pointQuestion P W sample.2)
          (fun A B =>
            evalOpt sample.1 sample.2
                (ProjectiveSetting.lineAnswerOrZero P sample.1 A) ≠
              some (ProjectiveSetting.pointAnswerOrZero B))) := by
  let X := LinePointSample P.toLdParams
  simpa only [ProjectiveSetting.lineEvalMeas, ProjectiveSetting.lineMeas,
    ProjectiveSetting.pointMeasOption, ProjectiveSetting.pointMeas,
    ProjectiveSetting.strategyMeasurement, Measurement.postprocess_comp] using
      consistencyDefect_postprocess_eq_mismatch (X := X) (linePointDist P.toLdParams) S.toStrategy
        (fun x => ProjectiveSetting.lineQuestion P W x.1)
        (fun x => ProjectiveSetting.pointQuestion P W x.2)
        (fun x a => evalOpt x.1 x.2 (ProjectiveSetting.lineAnswerOrZero P x.1 a))
        (fun _ b => some (ProjectiveSetting.pointAnswerOrZero b))

end

/-- The low-degree subtest bounds completed line-evaluation classes against
completed point measurements. This is item 2 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:200-204`, blueprint
`lem:qld-win-implications`. -/
theorem win_low_degree_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (linePointDist P.toLdParams)
        (fun sample => S.lineEvalMeas .alice W sample.1 sample.2)
        (fun sample => S.pointMeasOption .bob W sample.2)
        S.toStrategy.ψ ≤ 86 * ε := by
  intro P ε S _ W
  rw [lowDegreeConsistency_eq_mismatch]
  change avgOver (linePointDist P.toLdParams) (lowDegreeMismatchMass S W) ≤ _
  have h (k : LineKind) : avgOver (lineKindPointDist P.toLdParams k)
      (lowDegreeMismatchMass S W) ≤ 86 * ε := by
    rw [lineKindPointDist, Distribution.avgOver_map, ← avgOver_pauliToLd_uniform P W]
    exact (avgOver_mono _ _ _ (lineMismatch_le_rejection S k W)).trans
      (by simpa [pauli_edge_card] using fixedEdgeRejection_le_error S (linePointEdge k W))
  rw [linePointDist, avgOver_mix]
  linarith [h .axis, h .diagonal]

/-- Winning the point-versus-Pauli branch forces equality of evaluated labels. -/
theorem pauliBasisLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hwin : pauliWinPredicate P
      ((.point W), pauliCL P (.point W) z)
      ((.pauli W), pauliCL P (.pauli W) z) A B = true) :
    ProjectiveSetting.pointAnswerOrZero A =
      lowDegreeEnc (pauliAnswerOrZero B) (pauliToLd P W z).point := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i a h
  change a = lowDegreeEnc h (pauliToLd P W z).point
  simpa [pauliCL_point_eq, pauliPointPauliCondition,
    pauliPointBlock_contentOfPoint] using hwin.symm

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind)
include P ε S W

/-- Point/Pauli label mismatch is contained in rejection. -/
theorem pauliBasisMismatch_le_rejection (z : PauliSpace P) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.pauli W), pauliCL P (.pauli W) z)
        (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
          lowDegreeEnc (pauliAnswerOrZero B) (pauliToLd P W z).point) ≤
      pauliRejectionAt S.toStrategy
        (pointPauliEdge W) z :=
  mismatch_le_pauliRejectionAt S.toStrategy (pointPauliEdge W) z _ _ (fun A B => pauliBasisLabels_eq_of_win P W z A B)

/-- The uniform point mismatch average is the sampled point/Pauli branch average. -/
theorem avg_pauliBasisMismatch_eq_source :
    avgOver (uniformDistribution (PauliPoint P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W u) (pauliQuestion P W)
          (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
            lowDegreeEnc (pauliAnswerOrZero B) u)) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W (pauliToLd P W z).point)
          (pauliQuestion P W)
          (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
            lowDegreeEnc (pauliAnswerOrZero B) (pauliToLd P W z).point)) := by
  let f : (PauliPoint P) → ℝ := fun u =>
    outcomeEventWeight S.toStrategy
      (ProjectiveSetting.pointQuestion P W u) (pauliQuestion P W)
      (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
        lowDegreeEnc (pauliAnswerOrZero B) u)
  have hld := avgOver_pauliToLd_uniform P W
    (fun z => f z.point)
  have hpoint := avgOver_ldPoint_uniform P.toLdParams f
  exact (hld.trans hpoint).symm

/-- Pauli-basis consistency is the mismatch probability of the source answers. -/
theorem pauliBasisConsistency_eq_mismatch :
    bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeas .alice W)
        (S.pauliEvalMeas .bob W)
        S.toStrategy.ψ =
      avgOver (uniformDistribution (PauliPoint P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W u) (pauliQuestion P W)
          (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
            lowDegreeEnc (pauliAnswerOrZero B) u)) := by
  let X := PauliPoint P
  let qA : X → PauliQuestion P := fun u => ProjectiveSetting.pointQuestion P W u
  let qB : X → PauliQuestion P := fun _ => pauliQuestion P W
  let fA : X → PauliAnswer P → PauliScalar P := fun _ =>
    ProjectiveSetting.pointAnswerOrZero
  let fB : X → PauliAnswer P → PauliScalar P := fun u B =>
    lowDegreeEnc (pauliAnswerOrZero B) u
  refine (consistencyDefect_congr _ _ _ _ _ _ ?_ ?_).trans
    (consistencyDefect_postprocess_eq_mismatch
        (X := X) (uniformDistribution X) S.toStrategy qA qB fA fB)
  · intro u c
    rfl
  · intro u c
    congr 1
    unfold ProjectiveSetting.pauliEvalMeas ProjectiveSetting.pauliMeas fB qB
    rw [Measurement.postprocess_comp]
    rfl

end

/-- The Pauli-basis consistency subtest compares point values with evaluated
low-degree encodings of Pauli answers. This is item 3 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:205-209`, blueprint
`lem:qld-win-implications`. -/
theorem win_pauli_basis_cons_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeas .alice W)
        (S.pauliEvalMeas .bob W)
        S.toStrategy.ψ ≤ 86 * ε := by
  intro P ε S _ W
  rw [pauliBasisConsistency_eq_mismatch, avg_pauliBasisMismatch_eq_source]
  calc
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy
          (pointPauliEdge W)) := by
      apply avgOver_mono
      intro z
      have hs := pauliBasisMismatch_le_rejection S W z
      assumption
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε := fixedEdgeRejection_le_error S _
    _ = 86 * ε := by rw [pauli_edge_card]; norm_num

/-- A gated term dominated by a fixed-edge rejection on the conditioning event
is controlled by the original test's total rejection. -/
theorem avgOver_gated_le_fixedEdge {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (e : PauliEdge) (p : PauliTuple P → Prop) [DecidablePred p]
    (f : PauliTuple P → ℝ)
    (h : ∀ z, p (pauliSharedSplit P z).1 → f (pauliSharedSplit P z).1 ≤ pauliRejectionAt S.toStrategy e z) :
    avgOver (uniformDistribution (PauliTuple P)) (fun ω => if p ω then f ω else 0) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  rw [← avgOver_pauliTuple_uniform]
  refine (avgOver_mono _ _ _ fun z => ?_).trans (fixedEdgeRejection_le_error S e)
  split_ifs with hz
  · exact h z hz
  · exact pauliRejectionAt_nonneg S.toStrategy e z


end WinImplications

end

end MIPStarRE.QPBT
