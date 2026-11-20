module

public import QPBT.Observables.WinImplications.Commuting

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
def pointMsImplicationEdge : PauliKind → PauliEdge
  | .X => ⟨(.point .X, .ms (.var 0)), by simp [pauliEdges]⟩
  | .Z => ⟨(.point .Z, .ms (.var 4)), by simp [pauliEdges]⟩

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
  cases A <;> cases B <;>
    simp only [pauliWinPredicate, validPauliAnswer, Bool.and_true,
      Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, decide_eq_true_eq] at hwin
  rename_i a bit
  simp [pointTraceLabel, ProjectiveSetting.pointAnswerOrZero, ProjectiveSetting.pairWAnswerOrZero]
  have hgamma : pauliPairGamma P
      (pauliCL P (.ms (.var (selectedMsVar W))) z) ≠ 0 := by
    exact hanti
  rw [pauliCL_shared_eq P (.ms (.var (selectedMsVar W))) rfl] at hwin
  cases W with
  | X =>
      rcases hwin with hzero | hrest
      · exact (hgamma hzero).elim
      · aesop
  | Z =>
      rcases hwin with hzero | hrest
      · exact (hgamma hzero).elim
      · aesop

section

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind)

/-- Anticommuting point-trace/variable mismatch is contained in rejection. -/
theorem pointMsMismatch_le_rejection (z : PauliSpace P)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1) :
    outcomeEventWeight S.toStrategy
        ((.point W), pauliCL P (.point W) z)
        ((.ms (.var (selectedMsVar W))),
          pauliCL P (.ms (.var (selectedMsVar W))) z)
        (fun A B => pointTraceLabel P W (pauliSharedSplit P z).1 A ≠
          ProjectiveSetting.pairWAnswerOrZero B) ≤
      pauliRejectionAt S.toStrategy (pointMsImplicationEdge W) z := by
  cases W <;>
    apply outcome_event_weight_mono <;>
    intro A B hne <;>
    change pauliWinPredicate P _ _ A B = false <;>
    apply Bool.eq_false_iff.mpr <;>
    intro htrue <;>
    exact hne (pointMsLabels_eq_of_win P _ z A B hanti htrue)

/-- Point-trace/variable consistency is the mismatch probability of source answers. -/
theorem msConsConsistency_eq_mismatch :
    bipartiteDefect (anticommTupleDist P)
        (fun ω => S.pointTraceMeas .alice W (selectedTuplePoint W ω)
        (selectedTupleScalar W ω))
        (S.msVarBitMeas .bob (selectedMsVar W))
        S.toStrategy.ψ =
      avgOver (anticommTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W (selectedTuplePoint W ω))
          (ProjectiveSetting.msQuestion P (.var (selectedMsVar W))
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => pointTraceLabel P W ω A ≠
            ProjectiveSetting.pairWAnswerOrZero B)) := by
  have hmap : (msBitOrZero ∘
      ProjectiveSetting.msAnswerOrZero (.var (selectedMsVar W))) =
      ProjectiveSetting.pairWAnswerOrZero (P := P) := by
    funext B
    cases B <;> rfl
  rw [Function.comp_def] at hmap
  rw [← consistencyDefect_postprocess_eq_mismatch]
  refine congrArg₂ (fun A B => bipartiteDefect _ A B S.toStrategy.ψ) ?_ ?_ <;> funext x <;>
    first | rfl | simp only [ProjectiveSetting.pointTraceMeas, ProjectiveSetting.pointMeas, ProjectiveSetting.msVarBitMeas, ProjectiveSetting.msMeas, MIPStarRE.Quantum.Measurement.postprocess_comp, hmap] <;> rfl

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
        (fun ω => S.pointTraceMeas .alice W
        (match W with | .X => ω.1 | .Z => ω.2.1)
        (match W with | .X => ω.2.2.1 | .Z => ω.2.2.2))
        (S.msVarBitMeas .bob (match W with | .X => 0 | .Z => 4))
        S.toStrategy.ψ ≤ 16 * (Fintype.card PauliEdge : ℝ) * ε := by
  intro P ε S _ W
  change bipartiteDefect (anticommTupleDist P)
      (fun ω => S.pointTraceMeas .alice W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω))
      (S.msVarBitMeas .bob (selectedMsVar W))
      S.toStrategy.ψ ≤ _
  rw [msConsConsistency_eq_mismatch]
  calc
    _ ≤ _ := by
      apply avgOver_anticomm_le_sixteen_mul_gated
      intro ω
      apply outcome_event_weight_nonneg
    _ ≤ 16 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (pointMsImplicationEdge W)) := by
      gcongr
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      by_cases hanti : IsAnticommuting (pauliSharedSplit P z).1
      · simp_all
        solve_by_elim [pointMsMismatch_le_rejection]
      · simp_all
        apply pauliRejectionAt_nonneg
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _) (by norm_num)

section

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (z : PauliSpace P)
  (ω : PauliTuple P) (xy : MsType × MsType)
  (hxy : xy ∈ (graphDistribution msEdges_nonempty).support)
  (hanti : IsAnticommuting (pauliSharedSplit P z).1)

/-- Relabeling both Pauli answer measurements gives the induced Magic Square event mass. -/
theorem msRejection_eq_source (x y : MsType) :
    outcomeEventWeight (S.msStrategyAt ω) x y
        (fun a b => msWinPredicate x y a b = false) =
      outcomeEventWeight S.toStrategy
        (ProjectiveSetting.msQuestion P x ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (ProjectiveSetting.msQuestion P y ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (fun A B => msWinPredicate x y
          (ProjectiveSetting.msAnswerOrZero x A)
          (ProjectiveSetting.msAnswerOrZero y B) = false) := by
  let qx := ProjectiveSetting.msQuestion P x
    ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let qy := ProjectiveSetting.msQuestion P y
    ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  let fA :=
    ProjectiveSetting.msAnswerOrZero (P := P) x
  let fB :=
    ProjectiveSetting.msAnswerOrZero (P := P) y
  have hmass (a b : MsAnswer) :
      outcomeWeight (S.msStrategyAt ω) x y a b =
        ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
          ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
            outcomeWeight S.toStrategy qx qy A B := by
    have hop :
        heteroKron
            (∑ A ∈ Finset.univ.filter (fun A => fA A = a),
              (S.toStrategy.A qx).effect A)
            (∑ B ∈ Finset.univ.filter (fun B => fB B = b),
              (S.toStrategy.B qy).effect B) =
          ∑ A ∈ Finset.univ.filter (fun A => fA A = a),
            ∑ B ∈ Finset.univ.filter (fun B => fB B = b),
              heteroKron ((S.toStrategy.A qx).effect A)
                ((S.toStrategy.B qy).effect B) := by
      ext i j
      simp [Matrix.sum_apply, heteroKron, Matrix.kroneckerMap_apply]
      rw [Finset.sum_mul]
      simp [Finset.mul_sum]
    change DistanceCalculus.stateQForm S.toStrategy.ψ
        (heteroKron
          (((S.toStrategy.A qx).postprocess fA).effect a)
          (((S.toStrategy.B qy).postprocess fB).effect b)) = _
    simp only [MIPStarRE.Quantum.Measurement.postprocess_effect]
    rw [hop]
    simp [DistanceCalculus.stateQForm, applyOperatorToState, outcomeWeight]
  unfold outcomeEventWeight
  simp_rw [hmass]
  symm
  calc
    _ =
        _ := (Finset.sum_fiberwise Finset.univ fA (fun A =>
        ∑ B, if msWinPredicate x y (fA A) (fB B) = false then
          outcomeWeight S.toStrategy qx qy A B else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro A hA
      rw [(Finset.mem_filter.mp hA).2]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro A _
      exact (Finset.sum_fiberwise Finset.univ fB (fun B =>
        if msWinPredicate x y a (fB B) = false then
          outcomeWeight S.toStrategy qx qy A B else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro B hB
      rw [(Finset.mem_filter.mp hB).2]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1 with a
      simp

include hxy in
/-- Lift a supported Magic Square incidence to the corresponding Pauli verifier edge. -/
def msImplicationEdge : PauliEdge :=
  ⟨((.ms xy.1), (.ms xy.2)), by
    simp only [pauliEdges, Finset.union_assoc, Fin.zero_eta, Fin.isValue,
      Fin.reduceFinMk, Finset.union_insert, Finset.union_singleton,
      Finset.insert_union, Finset.mem_insert, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, reduceCtorEq, PauliType.ms.injEq, false_and,
      Prod.swap_prod_mk, and_false, or_self, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and, and_self, exists_const,
      Finset.mem_filter, Prod.exists, false_or]
    exact Or.inr ⟨xy.1, xy.2, ((Finset.mem_filter.mp hxy).2), Or.inl ⟨rfl, rfl⟩⟩⟩

/-- A relabeled Magic Square rejection on an anticommuting tuple is a Pauli rejection. -/
theorem msRejection_implies_pauliRejection
    (P : AdmissibleParams) (z : PauliSpace P) (xy : MsType × MsType)
    (hxy : xy ∈ (graphDistribution msEdges_nonempty).support)
    (hanti : IsAnticommuting (pauliSharedSplit P z).1)
    (A B : PauliAnswer P)
    (hreject : msWinPredicate xy.1 xy.2
      (ProjectiveSetting.msAnswerOrZero xy.1 A)
      (ProjectiveSetting.msAnswerOrZero xy.2 B) = false) :
    pauliWinPredicate P
      ((.ms xy.1), pauliCL P (.ms xy.1) z)
      ((.ms xy.2), pauliCL P (.ms xy.2) z) A B = false := by
  have hedge :=
    (Finset.mem_filter.mp hxy).2
  rcases Finset.mem_image.mp hedge with ⟨ik, _, heq⟩
  have hor :
      ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2))) = xy ∨
        ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2))) = xy.swap :=
    (Sym2.mk_eq_mk_iff).mp heq
  have hgamma (t : MsType) : pauliPairGamma P (pauliCL P (.ms t) z) ≠ 0 := by
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
        ((.var (msConstraintVars ik.1 ik.2), .constraint ik.1)) := by
      simpa using hswap.symm
    clear hreverse hswap hedge heq
    cases A <;> cases B <;>
      simp_all only [Finset.mem_univ, ne_eq, ProjectiveSetting.msAnswerOrZero,
        pauliWinPredicate, validPauliAnswer, Bool.and_self, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte, PauliType.ms.injEq,
        reduceCtorEq, exists_apply_eq_apply, or_self, decide_false]

/-- Rejection mass of the induced Magic Square strategy at one tuple and question pair. -/
noncomputable def inducedMsRejection : ℝ :=
  outcomeEventWeight (S.msStrategyAt ω) xy.1 xy.2
    (fun a b => msWinPredicate xy.1 xy.2 a b = false)

include hxy in
/-- The gated rejection average at a supported Magic Square incidence is bounded by
the rejection average of its fixed Pauli edge. -/
theorem gatedMsRejection_le_fixedEdge :
    avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsAnticommuting ω then inducedMsRejection S ω xy else 0) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  calc
    _ = _ := (avgOver_pauliTuple_uniform P (fun ω =>
        if IsAnticommuting ω then inducedMsRejection S ω xy else 0)).symm
    _ ≤ _ := by
      apply avgOver_mono
      intro z
      by_cases hanti : IsAnticommuting (pauliSharedSplit P z).1
      · simp_all
        rw [inducedMsRejection, msRejection_eq_source]
        have hs : outcomeEventWeight S.toStrategy ((.ms xy.1), pauliCL _ (.ms xy.1) z) ((.ms xy.2), pauliCL _ (.ms xy.2) z) (fun A B => msWinPredicate xy.1 xy.2 (ProjectiveSetting.msAnswerOrZero xy.1 A) (ProjectiveSetting.msAnswerOrZero xy.2 B) = false) ≤ pauliRejectionAt S.toStrategy (msImplicationEdge xy hxy) z := by
               apply outcome_event_weight_mono
               solve_by_elim [msRejection_implies_pauliRejection]
        exact hs
      · simp_all
        apply pauliRejectionAt_nonneg
    _ ≤ _ :=
      fixedEdgeRejection_le_error S _

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
  let ν := graphDistribution msEdges_nonempty
  have hpoint (ω : PauliTuple P) :
      avgOver ν (inducedMsRejection S ω) = 1 - S.msValueAt ω := by
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
        simp_all
  rw [hvalue, abs_of_nonneg]
  · calc
      _ ≤
          _ := by
        apply avgOver_anticomm_le_sixteen_mul_gated
        intro ω
        exact avgOver_nonneg ν _ fun xy =>
          outcome_event_weight_nonneg (S.msStrategyAt ω) xy.1 xy.2 _
      _ = 16 * avgOver ν (fun xy =>
          avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
            if IsAnticommuting ω then inducedMsRejection S ω xy else 0)) := by
        congr 1
        rw [← avgOver_comm _ _ _]
        apply avgOver_congr
        intro ω
        by_cases hanti : IsAnticommuting ω <;>
          simp [hanti, avgOver_zero]
      _ ≤ 16 * avgOver ν
          (fun _ => (Fintype.card PauliEdge : ℝ) * ε) := by
        gcongr
        apply avgOver_mono_on_support
        intro xy hxy
        solve_by_elim [gatedMsRejection_le_fixedEdge]
      _ = _ := by
        rw [avgOver_const_of_isProbability]
        · ring
        · apply Distribution.uniformOnFinset_isProbability
          obtain ⟨e, he⟩ := msEdges_nonempty
          obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective e
          change s(a, b) ∈ msEdges at he
          exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  · exact avgOver_nonneg (anticommTupleDist P) _ fun ω =>
      avgOver_nonneg ν _ fun xy =>
        outcome_event_weight_nonneg (S.msStrategyAt ω) xy.1 xy.2 _

end WinImplications

end

end MIPStarRE.QPBT
