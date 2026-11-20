module

public import QPBT.Observables.WinImplications.Commuting

public import QPBT.Games.AnswerTransport

/-!
# Magic Square winning implications

This module proves the exact induced Magic Square value and variable
consistency bounds on anticommuting Pauli tuples.

## References

The Magic Square value and consistency theorems prove items 6 and 7
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

/-- The verifier edge comparing a point trace with its Magic Square variable. -/
def pointMsImplicationEdge (W : PauliKind) : PauliEdge :=
  ⟨(.point W, .ms (.var (selectedMsVar W))), by cases W <;> simp [selectedMsVar, pauliEdges]⟩

/-- Winning the anticommuting point/variable branch forces equality of trace bits. -/
theorem pointMsLabels_eq_of_win (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (A B : PauliAnswer P)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1)
    (hwin : pauliWinPredicate P
      ((.point W), pauliCL P (.point W) z)
      ((.ms (.var (selectedMsVar W))),
        pauliCL P (.ms (.var (selectedMsVar W))) z) A B = true) :
    pointTraceLabel P W (pauliSharedSplit P z).1 A =
      ProjectiveSetting.pairWAnswerOrZero B := by
  have hg : pauliPairGamma P (pauliSharedProjection z) ≠ 0 := hanti
  cases A <;> cases B <;> simp [pauliWinPredicate, validPauliAnswer] at hwin
  change pauliPointVariableCondition P W (pauliSharedProjection z) (selectedMsVar W) _ _ at hwin
  cases W <;> simp [pauliPointVariableCondition, selectedMsVar, hg] at hwin <;>
    assumption

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind)
include P ε S W

/-- Anticommuting point-trace/variable mismatch is contained in rejection. -/
theorem pointMsMismatch_le_rejection (z : PauliSpace P)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.ms (.var (selectedMsVar W))),
          pauliCL P (.ms (.var (selectedMsVar W))) z)
        (fun A B => pointTraceLabel P W (pauliSharedSplit P z).1 A ≠
          ProjectiveSetting.pairWAnswerOrZero B) ≤
      pauliRejectionAt S.toStrategy (pointMsImplicationEdge W) z :=
  mismatch_le_pauliRejectionAt S.toStrategy (pointMsImplicationEdge W) z _ _
    (fun A B => pointMsLabels_eq_of_win P W z A B hanti)

/-- Point-trace/variable consistency is the mismatch probability of source answers. -/
theorem msConsConsistency_eq_mismatch :
    bipartiteDefect (anticommTupleDist P)
        (S.pointTraceAt .alice W)
        (fun ω => S.msVarBitMeas .bob (selectedMsVar W) ω)
        S.toStrategy.ψ =
      avgOver (anticommTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W (ω.point W))
          (ProjectiveSetting.msQuestion P (.var (selectedMsVar W))
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => pointTraceLabel P W ω A ≠
            ProjectiveSetting.pairWAnswerOrZero B)) := by
  refine pointTraceAt_defect_eq S W _ _ _ fun ω => ?_
  simp only [ProjectiveSetting.msVarBitMeas, ProjectiveSetting.msMeas, Measurement.postprocess_comp]
  congr 1
  funext a
  cases a <;> rfl

end

/-- On anticommuting tuples, the X and Z point traces agree respectively with
Magic Square variables 1 and 5. This is item 7 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:250-263`, blueprint
`lem:qld-win-implications`. -/
theorem win_ms_cons_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (anticommTupleDist P)
        (S.pointTraceAt .alice W)
        (S.msVarBitMeas .bob (selectedMsVar W))
        S.toStrategy.ψ ≤ 16 * (Fintype.card PauliEdge : ℝ) * ε := by
  intro P ε S _ W
  rw [msConsConsistency_eq_mismatch]
  refine (avgOver_anticomm_le_sixteen_mul_gated P _ (fun _ => outcome_event_weight_nonneg _ _ _ _)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (avgOver_gated_le_fixedEdge S (pointMsImplicationEdge W) _ _ ?_) (by norm_num)
  intro z hz
  have h := pointMsMismatch_le_rejection S W z hz
  rw [pauliCL_point_eq, pauliCL_shared_eq P (.ms (.var (selectedMsVar W))) rfl,
    pauliToLd_point_eq_selected] at h
  exact h

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε)

/-- Relabeling both Pauli answer measurements gives the induced Magic Square event mass. -/
theorem msRejection_eq_source (ω : PauliTuple P) (x y : MsType) :
    outcomeEventWeight (S.msStrategyAt ω) x y
        (fun a b => msWinPredicate x y a b = false) =
      outcomeEventWeight S.toStrategy
        (ProjectiveSetting.msQuestion P x ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (ProjectiveSetting.msQuestion P y ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (fun A B => msWinPredicate x y
          (ProjectiveSetting.msAnswerOrZero x A)
          (ProjectiveSetting.msAnswerOrZero y B) = false) := by
  exact outcomeEventWeight_postprocess S.toStrategy (S.msStrategyAt ω) _ _ x y
    (ProjectiveSetting.msAnswerOrZero x) (ProjectiveSetting.msAnswerOrZero y)
    (fun _ _ => rfl) _

/-- Lift a supported Magic Square incidence to the corresponding Pauli verifier edge. -/
def msImplicationEdge (xy : MsType × MsType)
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support) : PauliEdge :=
  ⟨((.ms xy.1), (.ms xy.2)), by
    have hedge := (Finset.mem_filter.mp hxy).2
    simp only [pauliEdges, Finset.union_assoc, Fin.zero_eta, Fin.isValue,
      Fin.reduceFinMk, Finset.union_insert, Finset.union_singleton,
      Finset.insert_union, Finset.mem_insert, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, reduceCtorEq, PauliType.ms.injEq, false_and,
      Prod.swap_prod_mk, and_false, or_self, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and, and_self, exists_const,
      Finset.mem_filter, Prod.exists, false_or]
    exact Or.inr ⟨xy.1, xy.2, hedge, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- A relabeled Magic Square rejection on an anticommuting tuple is a Pauli rejection. -/
theorem msRejection_implies_pauliRejection
    (P : AdmissibleParams) (z : PauliSpace P) (xy : MsType × MsType)
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1)
    (A B : PauliAnswer P)
    (hreject : msWinPredicate xy.1 xy.2
      (ProjectiveSetting.msAnswerOrZero xy.1 A)
      (ProjectiveSetting.msAnswerOrZero xy.2 B) = false) :
    pauliWinPredicate P
      ((.ms xy.1), pauliCL P (.ms xy.1) z)
      ((.ms xy.2), pauliCL P (.ms xy.2) z) A B = false := by
  have hedge := (Finset.mem_filter.mp hxy).2
  rcases Finset.mem_image.mp hedge with ⟨ik, _, heq⟩
  have hor :
      ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2)) :
          MsType × MsType) = xy ∨
        ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2)) :
          MsType × MsType) = xy.swap :=
    (Sym2.mk_eq_mk_iff (α := MsType)).mp heq
  have hgamma (t : MsType) : pauliPairGamma P (pauliCL P (.ms t) z) ≠ 0 := by
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) ≠ 0 at hanti
    rw [pauliCL_shared_eq P (.ms t) rfl]
    change gammaValue P (pauliXBlock z) (pauliZBlock z)
      (pauliRXBlock z) (pauliRZBlock z) ≠ 0
    exact hanti
  rcases hor with hforward | hreverse
  · subst xy
    cases A <;> cases B <;>
      simp_all only [Finset.mem_univ, ne_eq, ProjectiveSetting.msAnswerOrZero,
        pauliWinPredicate, validPauliAnswer, Bool.and_self, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte, PauliType.ms.injEq,
        reduceCtorEq, exists_apply_eq_apply, or_self, decide_false]
  · have hswap := congrArg Prod.swap hreverse
    have hxy : xy =
        ((.var (msConstraintVars ik.1 ik.2), .constraint ik.1) :
          MsType × MsType) := by
      simpa using hswap.symm
    subst xy
    clear hreverse hswap hedge heq
    cases A <;> cases B <;>
      simp_all only [Finset.mem_univ, ne_eq, ProjectiveSetting.msAnswerOrZero,
        pauliWinPredicate, validPauliAnswer, Bool.and_self, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte, PauliType.ms.injEq,
        reduceCtorEq, exists_apply_eq_apply, or_self, decide_false]

/-- At a supported Magic Square incidence, the induced rejection is contained in
the rejection at the corresponding fixed Pauli edge. -/
theorem msRejection_le_pauliRejection (z : PauliSpace P) (xy : MsType × MsType)
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.ms xy.1), pauliCL P (.ms xy.1) z)
        ((.ms xy.2), pauliCL P (.ms xy.2) z)
        (fun A B => msWinPredicate xy.1 xy.2
          (ProjectiveSetting.msAnswerOrZero xy.1 A)
          (ProjectiveSetting.msAnswerOrZero xy.2 B) = false) ≤
      pauliRejectionAt S.toStrategy (msImplicationEdge xy hxy) z := by
  apply outcome_event_weight_mono
  intro A B hreject
  exact msRejection_implies_pauliRejection P z xy hxy hanti A B hreject

/-- Rejection mass of the induced Magic Square strategy at one tuple and question pair. -/
noncomputable def inducedMsRejection (ω : PauliTuple P) (xy : MsType × MsType) : ℝ :=
  outcomeEventWeight (S.msStrategyAt ω) xy.1 xy.2
    (fun a b => msWinPredicate xy.1 xy.2 a b = false)

/-- The gated rejection average at a supported Magic Square incidence is bounded by
the rejection average of its fixed Pauli edge. -/
theorem gatedMsRejection_le_fixedEdge (xy : MsType × MsType)
    (hxy : xy ∈ (graphDistribution msEdges msEdges_nonempty).support) :
    avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsAnticommuting ω then inducedMsRejection S ω xy else 0) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  refine avgOver_gated_le_fixedEdge S (msImplicationEdge xy hxy) _ _ ?_
  intro z hz
  rw [inducedMsRejection, msRejection_eq_source]
  have h := msRejection_le_pauliRejection S z xy hxy hz
  rw [pauliCL_shared_eq P (.ms xy.1) rfl, pauliCL_shared_eq P (.ms xy.2) rfl] at h
  exact h

end

/-- The average value of the actual induced Magic Square strategies is close
to one on anticommuting tuples. This is item 6 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:240-249`, blueprint
`lem:qld-win-implications`. -/
theorem win_magic_square_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      |1 - avgOver (anticommTupleDist P) S.msValueAt| ≤
        16 * (Fintype.card PauliEdge : ℝ) * ε := by
  intro P ε S _
  let ν := graphDistribution msEdges msEdges_nonempty
  have hpoint (ω : PauliTuple P) :
      avgOver ν (inducedMsRejection S ω) = 1 - S.msValueAt ω := by
    change avgOver (graphDistribution msEdges msEdges_nonempty)
        (fun questions : MsType × MsType =>
          outcomeEventWeight (S.msStrategyAt ω) questions.1 questions.2
            (fun a b => msWinPredicate questions.1 questions.2 a b = false)) =
      1 - S.msValueAt ω
    convert rejectionEventAverage_eq_one_sub_value (S.msStrategyAt ω) using 1 <;>
      rfl
  have hvalue :
      1 - avgOver (anticommTupleDist P) S.msValueAt =
        avgOver (anticommTupleDist P) (fun ω =>
          avgOver ν (inducedMsRejection S ω)) := by
    calc
      _ = avgOver (anticommTupleDist P) (fun ω => 1 - S.msValueAt ω) := by
        symm
        rw [avgOver_sub, avgOver_const_of_isProbability _
          (anticommTupleDist_isProbability P)]
      _ = _ := by
        apply avgOver_congr
        intro ω
        exact (hpoint ω).symm
  rw [hvalue, abs_of_nonneg]
  · calc
      avgOver (anticommTupleDist P) (fun ω =>
          avgOver ν (inducedMsRejection S ω)) ≤
          16 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
            if IsAnticommuting ω then
              avgOver ν (inducedMsRejection S ω)
            else 0) := by
        apply avgOver_anticomm_le_sixteen_mul_gated
        intro ω
        exact avgOver_nonneg ν _ fun xy =>
          outcome_event_weight_nonneg (S.msStrategyAt ω) xy.1 xy.2 _
      _ = 16 * avgOver ν (fun xy =>
          avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
            if IsAnticommuting ω then inducedMsRejection S ω xy else 0)) := by
        congr 1
        calc
          avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
              if IsAnticommuting ω then
                avgOver ν (inducedMsRejection S ω)
              else 0) =
              avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
                avgOver ν (fun xy => if IsAnticommuting ω then
                  inducedMsRejection S ω xy else 0)) := by
            apply avgOver_congr
            intro ω
            by_cases hanti : IsAnticommuting ω <;>
              simp [hanti, avgOver_zero]
          _ = _ := avgOver_comm _ _ _
      _ ≤ 16 * avgOver ν
          (fun _ => (Fintype.card PauliEdge : ℝ) * ε) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply avgOver_mono_on_support
        intro xy hxy
        exact gatedMsRejection_le_fixedEdge S xy hxy
      _ = 16 * (Fintype.card PauliEdge : ℝ) * ε := by
        rw [avgOver_const_of_isProbability ν]
        · ring
        · exact graphDistribution_isProbability msEdges msEdges_nonempty
  · exact avgOver_nonneg (anticommTupleDist P) _ fun ω =>
      avgOver_nonneg ν _ fun xy =>
        outcome_event_weight_nonneg (S.msStrategyAt ω) xy.1 xy.2 _

end WinImplications

end

end MIPStarRE.QPBT
