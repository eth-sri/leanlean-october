module

public import QPBT.Observables.WinImplications.Interchange

/-!
# Transport of the winning implications to the interchanged tensor factor

This module carries the state-dependent functionals of the winning
implications across the interchange of the two tensor factors.  The
factor-interchanged conclusions of `lem:qld-win-implications` are stated with
the second player on the left factor and the reindexed state
`ProjectiveSetting.swappedState`; the lemmas here identify those quantities
with the ones proved on `S.toStrategy.psi`, so that the second pass of
`lem:qld-win-implications-obs` can reuse the first pass verbatim on the
interchanged side.

## References

The declarations support the trailing clause of `lem:qld-win-implications` and
the second assertion of `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:701-703`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:227,309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reindexing the identity and the strategy state -/

/-- Reindexing the identity operator gives the identity operator.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_one {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) : reindexOp e (1 : Op κ) = (1 : Op ι) := by
  ext i j
  simp [reindexOp, Matrix.one_apply, e.injective.eq_iff]

/-- The interchanged strategy state is again a unit vector.  This is needed to
chain consistency relations on the interchanged side of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`,
paper `14_analysis_of_the_pauli_basis_test.tex:227`. -/
theorem norm_swappedState {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) : ‖S.swappedState‖ = 1 := by
  have h := norm_applyOperatorToState_reindexState
    (Equiv.prodComm S.toStrategy.ιA S.toStrategy.ιB)
    (1 : Op (S.toStrategy.ιB × S.toStrategy.ιA)) S.toStrategy.ψ
  rw [reindexOp_one, applyOperatorToState_one, applyOperatorToState_one] at h
  rw [MIPStarRE.QPBT.ProjectiveSetting.swappedState, h]
  exact S.toStrategy.ψ_norm

/-! ## Transport of the consistency defect -/

/-- Left and right placements of local operators commute.  Formalization-only
support for `def:consistency`, blueprint `ch12_qpbt_games.tex:210-223`. -/
theorem heteroKron_left_right_comm {ιA ιB : Type*} [Fintype ιA]
    [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] (A : Op ιA) (B : Op ιB) :
    heteroKron A (1 : Op ιB) * heteroKron (1 : Op ιA) B =
      heteroKron (1 : Op ιA) B * heteroKron A 1 := by
  rw [heteroKron_mul, heteroKron_mul, mul_one, one_mul, one_mul, mul_one]

/-- Reindexing an operator along an equivalence is multiplicative.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M N : Op κ) :
    reindexOp e (M * N) = reindexOp e M * reindexOp e N := by
  ext i j
  change (M * N) (e i) (e j) = ∑ k : ι, M (e i) (e k) * N (e k) (e j)
  rw [Matrix.mul_apply, ← e.sum_comp (fun l : κ => M (e i) l * N l (e j))]

/-- The real quadratic form is invariant under simultaneous reindexing of the
state and operator. Formalization-only support for the interchanged conclusions
of blueprint `lem:qld-win-implications`; see
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:227`. -/
theorem stateQForm_reindexState {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (T : Op κ)
    (ψ : EuclideanSpace ℂ ι) :
    DistanceCalculus.stateQForm (reindexState e ψ) T =
      DistanceCalculus.stateQForm ψ (reindexOp e T) := by
  have hstate (k : κ) : (reindexState e ψ).ofLp k = ψ.ofLp (e.symm k) := rfl
  have hstate_star (k : κ) : star (reindexState e ψ).ofLp k =
      star (ψ.ofLp (e.symm k)) := congrArg star (hstate k)
  have hop (i j : ι) : reindexOp e T i j = T (e i) (e j) := rfl
  unfold DistanceCalculus.stateQForm applyOperatorToState
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (Complex.re (∑ k : κ,
      (∑ l : κ, T k l * (reindexState e ψ).ofLp l) *
        star (reindexState e ψ).ofLp k)) =
    Complex.re (∑ i : ι, (∑ l : ι, reindexOp e T i l * ψ.ofLp l) *
      star (ψ.ofLp i))
  simp_rw [hop, hstate, hstate_star]
  apply congrArg Complex.re
  have hinner (i : ι) : (∑ l : ι, T (e i) (e l) * ψ.ofLp l) =
      ∑ l : κ, T (e i) l * ψ.ofLp (e.symm l) := by
    rw [← e.sum_comp (fun l : κ => T (e i) l * ψ.ofLp (e.symm l))]
    exact Finset.sum_congr rfl (fun l _ => by rw [e.symm_apply_apply])
  calc
    (∑ k : κ, (∑ l : κ, T k l * ψ.ofLp (e.symm l)) *
        star (ψ.ofLp (e.symm k))) =
        ∑ i : ι, (∑ l : κ, T (e i) l * ψ.ofLp (e.symm l)) *
          star (ψ.ofLp (e.symm (e i))) :=
      (e.sum_comp (fun k : κ => (∑ l : κ, T k l * ψ.ofLp (e.symm l)) *
        star (ψ.ofLp (e.symm k)))).symm
    _ = ∑ i : ι, (∑ l : ι, T (e i) (e l) * ψ.ofLp l) * star (ψ.ofLp i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hinner i, e.symm_apply_apply]

/-- The consistency defect of two oppositely placed families is unchanged by
interchanging the tensor factors of both the families and the state.  This is
the transport carrying the interchanged clause of `lem:qld-win-implications`
to the interchanged state, blueprint `ch14_qpbt_observables.tex:701-703`,
paper `14_analysis_of_the_pauli_basis_test.tex:227`. -/
theorem consistencyDefect_swappedState {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (M : X → α → Op ιA) (N : X → α → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ (fun x a => heteroKron (N x a) 1)
        (fun x a => heteroKron 1 (M x a))
        (reindexState (Equiv.prodComm ιA ιB) ψ) =
      consistencyDefect μ (fun x a => heteroKron (M x a) 1)
        (fun x a => heteroKron 1 (N x a)) ψ := by
  classical
  unfold consistencyDefect
  refine avgOver_congr _ _ _ ?_
  intro x
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  by_cases hab : b = a
  · simp [hab]
  · have hba : a ≠ b := fun h => hab h.symm
    simp only [if_neg hab, if_neg hba]
    rw [DistanceCalculus.consistency_term_eq_stateQForm,
      DistanceCalculus.consistency_term_eq_stateQForm,
      stateQForm_reindexState, reindexOp_mul,
      reindexOp_prodComm_heteroKron, reindexOp_prodComm_heteroKron,
      heteroKron_left_right_comm]

/-! ## Transport of the phase-signed operator distance -/

/-- Reindexing an operator commutes with scalar multiplication.
Formalization-only support for the second assertion of
`lem:qld-win-implications-obs`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem reindexOp_smul {ι κ : Type*} (e : ι ≃ κ) (c : ℂ) (M : Op κ) :
    reindexOp e (c • M) = c • reindexOp e M := rfl

/-- The phase-signed operator distance of two left-placed families is
unchanged by interchanging the tensor factors of the families and the state.
This is the transport used by the second assertion of
`lem:qld-win-implications-obs`, blueprint
`ch14_qpbt_observables.tex:761-794`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`. -/
theorem opDistSq_smul_swappedState {X ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (c : X → ℂ) (M N : X → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opDistSq μ (fun x => heteroKron (M x) (1 : Op ιA))
        (fun x => c x • heteroKron (N x) (1 : Op ιA))
        (reindexState (Equiv.prodComm ιA ιB) ψ) =
      opDistSq μ (fun x => heteroKron (1 : Op ιA) (M x))
        (fun x => c x • heteroKron (1 : Op ιA) (N x)) ψ := by
  unfold opDistSq opFamilyDistSq
  refine avgOver_congr _ _ _ ?_
  intro x
  refine Finset.sum_congr rfl ?_
  intro _ _
  rw [norm_applyOperatorToState_reindexState]
  congr 2
  rw [reindexOp_sub, reindexOp_smul, reindexOp_prodComm_heteroKron,
    reindexOp_prodComm_heteroKron]

noncomputable def pauliStrategySwap {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) : Strategy (pauliBasisTest P) where
  ιA := S.ιB
  ιB := S.ιA
  ψ := reindexState (Equiv.prodComm S.ιA S.ιB) S.ψ
  ψ_norm := by
    have h := norm_applyOperatorToState_reindexState
      (Equiv.prodComm S.ιA S.ιB) (1 : Op (S.ιB × S.ιA)) S.ψ
    rwa [reindexOp_one, applyOperatorToState_one, applyOperatorToState_one, S.ψ_norm] at h
  A := S.B
  B := S.A

set_option maxRecDepth 20000 in
theorem pauliStrategySwap_value {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) :
    (pauliStrategySwap S).value = S.value := by
  classical
  have hout (x y : PauliQuestion P) (a b : PauliAnswer P) :
      outcomeWeight (pauliStrategySwap S) x y a b = outcomeWeight S y x b a := by
    change DistanceCalculus.stateQForm (reindexState (Equiv.prodComm S.ιA S.ιB) S.ψ)
        (heteroKron ((S.B x).effect a) ((S.A y).effect b)) =
      DistanceCalculus.stateQForm S.ψ
        (heteroKron ((S.A y).effect b) ((S.B x).effect a))
    rw [stateQForm_reindexState, reindexOp_prodComm_heteroKron]
  have havg (T : Strategy (pauliBasisTest P)) :
      avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt T ez.1 ez.2) = 1 - T.value := by
    rw [← rejectionEventAverage_eq_one_sub_value T]
    unfold pauliBasisTest pauliQuestionDistribution
    rw [Distribution.avgOver_map]
    rfl
  let swapEdge : PauliEdge ≃ PauliEdge :=
    { toFun e := ⟨e.1.swap, by simpa [Sym2.eq_swap] using e.2⟩
      invFun e := ⟨e.1.swap, by simpa [Sym2.eq_swap] using e.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hrej : avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt (pauliStrategySwap S) ez.1 ez.2) =
      avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt S ez.1 ez.2) := by
    rw [avgOver_eq_sum_univ, avgOver_eq_sum_univ,
      ← (swapEdge.prodCongr (Equiv.refl (PauliSpace P))).sum_comp]
    refine Finset.sum_congr rfl fun ⟨e, z⟩ _ => ?_
    have hw : (uniformDistribution (PauliEdge × PauliSpace P)).weight
        ((swapEdge.prodCongr (Equiv.refl (PauliSpace P))) (e, z)) =
        (uniformDistribution (PauliEdge × PauliSpace P)).weight (e, z) := by
      simp [uniformDistribution, Distribution.uniformOnFinset_weight]
    rw [hw]
    congr 1
    unfold pauliRejectionAt outcomeEventWeight pauliSourceQuestions
    dsimp [swapEdge]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change (if pauliWinPredicate P (e.1.2, pauliCL P e.1.2 z) (e.1.1, pauliCL P e.1.1 z) b a = false
        then outcomeWeight (pauliStrategySwap S) (e.1.2, pauliCL P e.1.2 z)
          (e.1.1, pauliCL P e.1.1 z) b a else 0) =
      if pauliWinPredicate P (e.1.1, pauliCL P e.1.1 z) (e.1.2, pauliCL P e.1.2 z) a b = false then
        outcomeWeight S (e.1.1, pauliCL P e.1.1 z) (e.1.2, pauliCL P e.1.2 z) a b else 0
    rw [pauliWinPredicate_symm P _ _ b a, hout]
  linarith [havg (pauliStrategySwap S), havg S]

/-- The interchanged projective setting with Alice and Bob swapped. -/
noncomputable def _root_.MIPStarRE.QPBT.ProjectiveSetting.swap
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) :
    ProjectiveSetting P ε where
  toStrategy := pauliStrategySwap S.toStrategy
  isProjective := ⟨S.isProjective.2, S.isProjective.1⟩
  win := by rw [pauliStrategySwap_value]; exact S.win

end WinImplications

end

end MIPStarRE.QPBT
