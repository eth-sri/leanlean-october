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

local instance (priority := 10) {α β : Type*} (r : α → β → Prop) :
    DecidableRel r :=
  fun a b => Classical.propDecidable (r a b)

section

variable (P : AdmissibleParams)

local instance linePointFintypeCanonical :
    Fintype (LineDesc P.toLdParams ×
      (LdPoint P.toLdParams)) :=
  linePointFintype P

/-- Coordinates outside one low-degree register in the Pauli seed. -/
abbrev PauliLdRemainder :=
  (PauliPoint P) × PauliScalar P × PauliScalar P

/-- Split a Pauli seed into a basis-selected low-degree seed and unused coordinates. -/
private def pauliLdSplit (W : PauliKind) :
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
abbrev PauliSharedRemainder :=
  PauliScalar P × (PauliPoint P)

/-- Split a Pauli seed into its shared tuple and discarded scalar/direction blocks. -/
def pauliSharedSplit :
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
  right_inv zr := by
    rcases zr with ⟨⟨uX, uZ, rX, rZ⟩, scalar, direction⟩
    rfl

end

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
  right_inv zr := by
    rcases zr with ⟨point, seed, direction⟩
    rfl

/-- Uniform Pauli seeds have the uniform low-degree marginal in either basis. -/
theorem avgOver_pauliToLd_uniform {P : AdmissibleParams} (W : PauliKind)
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

section

variable (P : AdmissibleParams)

/-- The point conditioning map produces the typed point content. -/
theorem pauliCL_point_eq (W : PauliKind)
    (z : PauliSpace P) :
    pauliCL P (.point W) z =
      ProjectiveSetting.contentOfPoint P W (pauliToLd P W z).point := by
  rfl

/-- The shared conditioning map produces the typed tuple content. -/
theorem pauliCL_shared_eq (t : PauliType)
    (ht : pauliCL P t = pauliSharedProjection) (z : PauliSpace P) :
    pauliCL P t z = ProjectiveSetting.contentOfTuple P
      (pauliXBlock z) (pauliZBlock z) (pauliRXBlock z) (pauliRZBlock z) := by
  aesop

/-- Reading a typed point content recovers its point block. -/
theorem pauliPointBlock_contentOfPoint
    (W : PauliKind) (u : PauliPoint P) :
    pauliPointBlock W (ProjectiveSetting.contentOfPoint P W u) = u := by
  cases W <;> rfl

section

variable (W : PauliKind) (line : LineDesc P.toLdParams)

/-- Reading a typed line content recovers its canonical base. -/
theorem pauliPointBlock_contentOfLine :
    pauliPointBlock W (ProjectiveSetting.contentOfLine P W line) = line.base := by
  cases W <;> rfl

/-- Reading a typed line content recovers its geometric direction. -/
theorem pauliDirectionBlock_contentOfLine
    (hline : line.kind = .diagonal) :
    pauliDirectionBlock (ProjectiveSetting.contentOfLine P W line) = line.direction := by
  funext j
  cases line with
  | axis => simp_all [LineDesc.kind]
  | diagonal => rfl

end

end

/-- Zero-padding a coefficient list does not change its polynomial value. -/
theorem evalCoefficient_padTo {L : LdParams} {c c' : ℕ} (h : c ≤ c')
    (f : DegPoly L c) (t : ScalarQ L) :
    evalCoefficient (DegPoly.padTo h f) t = evalCoefficient f t := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
      have heq : DegPoly.padTo h f = f := by
        funext i
        simp [DegPoly.padTo, i.isLt]
      rw [heq]
  | succ k ih =>
      rw [evalCoefficient, Fin.sum_univ_castSucc]
      have hcast :
          (∑ i : Fin (c + (k + 1)),
              DegPoly.padTo h f i.castSucc * t ^ i.castSucc.val) =
            evalCoefficient (DegPoly.padTo (Nat.le_add_right c k) f) t := by
        rfl
      simp_all [ih, DegPoly.padTo]

/-- A uniquely determined line evaluation is returned by `evalOpt`. -/
theorem evalOpt_eq_some_of_evaluatesTo {L : LdParams} {c : ℕ}
    (line : LineDesc L) (f : DegPoly L c) (u : LdPoint L)
    (a : ScalarQ L) (h : EvaluatesTo line f u a) :
    evalOpt line u f = some a := by
  unfold evalOpt
  rw [dif_pos]
  apply congrArg some
  obtain ⟨t, ht⟩ := h.1
  exact ((Classical.choose_spec ⟨a, h⟩).2 t ht).symm.trans (h.2 t ht)

section

variable (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P)

/-- The sampled point lies on its canonical diagonal line. -/
theorem point_mem_sampled_dline :
    (pauliToLd P W z).point ∈
      (dLineDescOf
        (ldDLineCL P.toLdParams (pauliToLd P W z))).pointSet := by
  change _ ∈ linePoints
    (lineRepMap
      (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction))
      (lineRepMap
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction) (pauliToLd P W z).point))
    (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
      (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (pauliToLd P W z).direction))
  rw [prefixProjection_idempotent, lineRepMap_apply_self]
  apply mem_linePoints_lineRepMap

/-- The axis-line conditioning map produces the typed canonical line content. -/
theorem pauliCL_aline_eq :
    pauliCL P (.aline W) z = ProjectiveSetting.contentOfLine P W
      (aLineDescOf (ldALineCL P.toLdParams (pauliToLd P W z))) := by
  apply congrArg (embedLd P W)
  funext i
  rcases i with (j | u) | j
  · change (lineRepMap
        (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
        (pauliToLd P W z).point) j =
      (lineRepMap
        (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
        (lineRepMap
          (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
          (pauliToLd P W z).point)) j
    rw [lineRepMap_apply_self]
  all_goals rfl

/-- The diagonal-line conditioning map produces the typed canonical line content. -/
theorem pauliCL_dline_eq :
    pauliCL P (.dline W) z = ProjectiveSetting.contentOfLine P W
      (dLineDescOf (ldDLineCL P.toLdParams (pauliToLd P W z))) := by
  apply congrArg (embedLd P W)
  funext i
  rcases i with (j | u) | j
  · change (lineRepMap
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction) (pauliToLd P W z).point) j =
      (lineRepMap
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
            (pauliToLd P W z).direction))
        (lineRepMap
          (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
            (pauliToLd P W z).direction) (pauliToLd P W z).point)) j
    rw [prefixProjection_idempotent, lineRepMap_apply_self]
  · rfl
  · change prefixProjection _
        (pauliToLd P W z).direction j =
      prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction) j
    rw [prefixProjection_idempotent]

/-- A successful sampled axis-line check gives the corresponding evaluation identity. -/
theorem aline_winning_condition (f : Fin (P.d + 1) → PauliScalar P)
    (a : PauliScalar P)
    (hwin : pauliWinPredicate P
      ((.aline W), pauliCL P (.aline W) z)
      ((.point W), pauliCL P (.point W) z)
      (.alinePoly f) (.value a) = true) :
    ∀ t : ScalarQ P.toLdParams,
      (pauliToLd P W z).point =
          (aLineDescOf
            (ldALineCL P.toLdParams (pauliToLd P W z))).base +
            t • (aLineDescOf
              (ldALineCL P.toLdParams (pauliToLd P W z))).direction →
        evalCoefficient f t = a := by
  rw [pauliCL_aline_eq, pauliCL_point_eq] at hwin
  have hc : pauliAlinePointCondition P W
      (ProjectiveSetting.contentOfLine P W
        (aLineDescOf (ldALineCL P.toLdParams (pauliToLd P W z))))
      (ProjectiveSetting.contentOfPoint P W (pauliToLd P W z).point) f a := by
    simpa [pauliWinPredicate, validPauliAnswer] using hwin
  intro t ht
  apply hc t
  simp [pauliPointBlock_contentOfPoint, pauliPointBlock_contentOfLine]
  assumption

/-- A successful sampled diagonal-line check gives the corresponding evaluation identity. -/
theorem dline_winning_condition (f : Fin (P.m * P.d + 1) → PauliScalar P)
    (a : PauliScalar P)
    (hwin : pauliWinPredicate P
      ((.dline W), pauliCL P (.dline W) z)
      ((.point W), pauliCL P (.point W) z)
      (.dlinePoly f) (.value a) = true) :
    ∀ t : ScalarQ P.toLdParams,
      (pauliToLd P W z).point =
          (dLineDescOf
            (ldDLineCL P.toLdParams (pauliToLd P W z))).base +
            t • (dLineDescOf
              (ldDLineCL P.toLdParams (pauliToLd P W z))).direction →
        evalCoefficient f t = a := by
  rw [pauliCL_dline_eq, pauliCL_point_eq] at hwin
  have hc : pauliDlinePointCondition P W
      (ProjectiveSetting.contentOfLine P W
        (dLineDescOf (ldDLineCL P.toLdParams (pauliToLd P W z))))
      (ProjectiveSetting.contentOfPoint P W (pauliToLd P W z).point) f a := by
    simpa [pauliWinPredicate, validPauliAnswer] using hwin
  intro t ht
  apply hc t
  simp [pauliPointBlock_contentOfPoint, pauliPointBlock_contentOfLine, pauliDirectionBlock_contentOfLine]
  assumption

/-- Winning the sampled axis-line branch forces equality of the exposed labels. -/
theorem alineLabels_eq_of_win (A B : PauliAnswer P)
    (hwin : pauliWinPredicate P
      ((.aline W), pauliCL P (.aline W) z)
      ((.point W), pauliCL P (.point W) z) A B = true) :
    evalOpt
        (aLineDescOf (ldALineCL P.toLdParams (pauliToLd P W z)))
        (pauliToLd P W z).point
        (ProjectiveSetting.lineAnswerOrZero
          (aLineDescOf (ldALineCL P.toLdParams (pauliToLd P W z))) A) =
      some (ProjectiveSetting.pointAnswerOrZero B) := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i f a
  apply evalOpt_eq_some_of_evaluatesTo
  refine ⟨(by
            change (pauliToLd P W z).point ∈ linePoints
              (lineRepMap
                (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
                (lineRepMap
                  (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
                  (pauliToLd P W z).point))
              (coordinateDirection (chiIndex P.toLdParams (pauliToLd P W z).seed))
            rw [lineRepMap_apply_self]
            apply mem_linePoints_lineRepMap), ?_⟩
  intro t ht
  let hpad :=
    Nat.le_mul_of_pos_left P.d (Nat.zero_lt_of_lt P.one_le_m)
  rw [show ProjectiveSetting.lineAnswerOrZero
      (aLineDescOf (ldALineCL P.toLdParams (pauliToLd P W z)))
      (.alinePoly f) = DegPoly.padTo hpad f by rfl, evalCoefficient_padTo hpad]
  exact aline_winning_condition P W z f a (by
    simpa [pauliWinPredicate, validPauliAnswer] using hwin) t ht

/-- Winning the sampled diagonal-line branch forces equality of exposed labels. -/
theorem dlineLabels_eq_of_win (A B : PauliAnswer P)
    (hwin : pauliWinPredicate P
      ((.dline W), pauliCL P (.dline W) z)
      ((.point W), pauliCL P (.point W) z) A B = true) :
    evalOpt
        (dLineDescOf (ldDLineCL P.toLdParams (pauliToLd P W z)))
        (pauliToLd P W z).point
        (ProjectiveSetting.lineAnswerOrZero
          (dLineDescOf (ldDLineCL P.toLdParams (pauliToLd P W z))) A) =
      some (ProjectiveSetting.pointAnswerOrZero B) := by
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i f a
  apply evalOpt_eq_some_of_evaluatesTo
  refine ⟨point_mem_sampled_dline P W z, ?_⟩
  intro t ht
  exact dline_winning_condition P W z f a (by
    simpa [pauliWinPredicate, validPauliAnswer] using hwin) t ht

end

section

variable (W : PauliKind)

/-- The axis-line/point verifier edge in one Pauli basis. -/
def alinePointEdge : PauliEdge :=
  ⟨(.aline W, .point W), by simp [pauliEdges]⟩

/-- The diagonal-line/point verifier edge in one Pauli basis. -/
def dlinePointEdge : PauliEdge :=
  ⟨(.dline W, .point W), by simp [pauliEdges]⟩

/-- The point/Pauli verifier edge in one Pauli basis. -/
def pointPauliEdge : PauliEdge :=
  ⟨(.point W, .pauli W), by simp [pauliEdges]⟩

/-- The Pair-W/Pair verifier edge in one Pauli basis. -/
def pairWPairEdge : PauliEdge :=
  ⟨(.pairW W, .pair), by simp [pauliEdges]⟩

/-- The point/Pair-W verifier edge in one Pauli basis. -/
def pointPairWEdge : PauliEdge :=
  ⟨(.point W, .pairW W), by simp [pauliEdges]⟩

end

section

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind)

/-- Source-answer mismatch mass for the completed line and point readouts. -/
noncomputable def lowDegreeMismatchMass
    (sample : LineDesc P.toLdParams × (PauliPoint P)) : ℝ :=
  outcomeEventWeight S.toStrategy
    (ProjectiveSetting.lineQuestion P W sample.1)
    (ProjectiveSetting.pointQuestion P W sample.2)
    (fun A B =>
      evalOpt sample.1 sample.2
          (ProjectiveSetting.lineAnswerOrZero sample.1 A) ≠
        some (ProjectiveSetting.pointAnswerOrZero B))

/-- The axis component of the exposed line sampler is the corresponding Pauli branch. -/
theorem avg_alineMismatch_eq_source :
    avgOver (aLinePointDist P.toLdParams) (lowDegreeMismatchMass S W) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          ((.aline W), pauliCL P (.aline W) z)
          ((.point W), pauliCL P (.point W) z)
          (fun A B =>
            evalOpt
                (aLineDescOf
                  (ldALineCL P.toLdParams (pauliToLd P W z)))
                (pauliToLd P W z).point
                (ProjectiveSetting.lineAnswerOrZero
                  (aLineDescOf
                    (ldALineCL P.toLdParams (pauliToLd P W z))) A) ≠
              some (ProjectiveSetting.pointAnswerOrZero B))) := by
  unfold aLinePointDist clDistribution
  simp [Distribution.avgOver_map]
  rw [← avgOver_pauliToLd_uniform]
  apply avgOver_congr
  intro z
  simp [pauliCL_aline_eq]
  rfl

/-- The diagonal component of the exposed line sampler is the corresponding Pauli branch. -/
theorem avg_dlineMismatch_eq_source :
    avgOver (dLinePointDist P.toLdParams) (lowDegreeMismatchMass S W) =
      avgOver (uniformDistribution (PauliSpace P)) (fun z =>
        outcomeEventWeight S.toStrategy
          ((.dline W), pauliCL P (.dline W) z)
          ((.point W), pauliCL P (.point W) z)
          (fun A B =>
            evalOpt
                (dLineDescOf
                  (ldDLineCL P.toLdParams (pauliToLd P W z)))
                (pauliToLd P W z).point
                (ProjectiveSetting.lineAnswerOrZero
                  (dLineDescOf
                    (ldDLineCL P.toLdParams (pauliToLd P W z))) A) ≠
              some (ProjectiveSetting.pointAnswerOrZero B))) := by
  unfold dLinePointDist clDistribution
  simp [Distribution.avgOver_map]
  rw [← avgOver_pauliToLd_uniform]
  apply avgOver_congr
  intro z
  simp [pauliCL_dline_eq]
  rfl

/-- The completed low-degree consistency defect is its source-answer mismatch mass. -/
theorem lowDegreeConsistency_eq_mismatch :
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
                (ProjectiveSetting.lineAnswerOrZero sample.1 A) ≠
              some (ProjectiveSetting.pointAnswerOrZero B))) := by
  rw [← consistencyDefect_postprocess_eq_mismatch]
  refine congrArg₂ (fun A B => bipartiteDefect _ A B S.toStrategy.ψ) ?_ ?_ <;> funext x <;>
    first | rfl | simp only [ProjectiveSetting.lineEvalMeas, ProjectiveSetting.lineMeas, ProjectiveSetting.pointMeasOption, ProjectiveSetting.pointMeas, MIPStarRE.Quantum.Measurement.postprocess_comp] <;> rfl

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
  change avgOver _ (lowDegreeMismatchMass S W) ≤ _
  have ha : avgOver (aLinePointDist P.toLdParams) (lowDegreeMismatchMass S W) ≤
      (Fintype.card PauliEdge) * ε := by
    rw [avg_alineMismatch_eq_source]
    calc
      _ ≤ avgOver (uniformDistribution (PauliSpace P))
          (pauliRejectionAt S.toStrategy
            (alinePointEdge W)) := by
        apply avgOver_mono
        intro z
        apply outcome_event_weight_mono
        intro A B hne
        change _ = false
        apply Bool.eq_false_iff.mpr
        solve_by_elim [alineLabels_eq_of_win]
      _ ≤ _ :=
        fixedEdgeRejection_le_error S _
  have hd : avgOver (dLinePointDist P.toLdParams) (lowDegreeMismatchMass S W) ≤
      (Fintype.card PauliEdge) * ε := by
    rw [avg_dlineMismatch_eq_source]
    calc
      _ ≤ avgOver (uniformDistribution (PauliSpace P))
          (pauliRejectionAt S.toStrategy
            (dlinePointEdge W)) := by
        apply avgOver_mono
        intro z
        apply outcome_event_weight_mono
        intro A B hne
        change _ = false
        apply Bool.eq_false_iff.mpr
        solve_by_elim [dlineLabels_eq_of_win]
      _ ≤ _ :=
        fixedEdgeRejection_le_error S _
  rw [linePointDist, avgOver_mix]
  rw [pauli_edge_card] at ha hd
  norm_num at ha hd
  linarith

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

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind)

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
  let f : _ → ℝ := fun u =>
    outcomeEventWeight S.toStrategy
      (ProjectiveSetting.pointQuestion P W u) (pauliQuestion P W)
      (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
        lowDegreeEnc (pauliAnswerOrZero B) u)
  exact ((avgOver_pauliToLd_uniform W
    (fun z => f z.point)).trans (avgOver_ldPoint_uniform P.toLdParams f)).symm

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
  rw [← consistencyDefect_postprocess_eq_mismatch]
  refine congrArg₂ (fun A B => bipartiteDefect _ A B S.toStrategy.ψ) ?_ ?_ <;> funext x <;>
    first | rfl | simp only [ProjectiveSetting.pauliEvalMeas, ProjectiveSetting.pauliMeas, MIPStarRE.Quantum.Measurement.postprocess_comp] <;> rfl

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
    _ ≤ _ := by
      apply avgOver_mono
      intro z
      have hs : outcomeEventWeight S.toStrategy ((.point W), pauliCL _ (.point W) z) ((.pauli W), pauliCL _ (.pauli W) z) (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠ lowDegreeEnc (pauliAnswerOrZero B) (pauliToLd _ W z).point) ≤ pauliRejectionAt S.toStrategy (pointPauliEdge W) z := by
             apply outcome_event_weight_mono
             intro A B hne
             change pauliWinPredicate _ _ _ A B = false
             apply Bool.eq_false_iff.mpr
             intro htrue
             exact hne (pauliBasisLabels_eq_of_win _ W z A B htrue)
      assumption
    _ ≤ _ := fixedEdgeRejection_le_error S _
    _ = 86 * ε := by simp [pauli_edge_card]

end WinImplications

end

end MIPStarRE.QPBT
