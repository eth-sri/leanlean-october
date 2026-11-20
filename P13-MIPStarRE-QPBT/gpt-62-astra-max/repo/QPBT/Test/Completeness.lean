module

public import QPBT.Test.Completeness.Rejection
public import QPBT.Test.LowDegreeGameMeasurements
public import QPBT.Test.PauliSymmetry

/-!
# Completeness of the Pauli basis test

The Pauli basis test admits a symmetric presentation and a value-one SPCC
strategy.

## References

The source statement is blueprint
`lem:pauli-completeness`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

variable (P : AdmissibleParams) (x y : PauliQuestion P)
  (hxy : 0 < (pauliQuestionDistribution P).weight (x, y)) (a b : PauliAnswer P)

/-- The honest strategy of `lem:pauli-completeness`: the total honest
measurement family of `MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily`
on the maximally entangled state of the Pauli register tensored with the Magic
Square qubit.  Blueprint `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1237-1360`. -/
noncomputable def honestStrategy :
    SymmetricStrategy (pauliBasisTestSymm P) where
  ι := HonestIndex P
  ψ := eprState (HonestIndex P)
  ψ_norm := eprState_norm (HonestIndex P)
  ψ_swap := reindexState_prodComm_eprState (HonestIndex P)
  M := fun q => honestMeasurement q.1 q.2

/-- Every measurement of the honest strategy is projective. -/
theorem honestStrategy_projective :
    MIPStarRE.QPBT.Measurement.IsProjective ((honestStrategy P).M x) :=
  honestMeasurement_projective P x.1 x.2

/-- The honest strategy is a symmetric projective consistent commuting
strategy: every measurement is projective, the family is consistent on the
maximally entangled state, and the effects commute on every question pair of
positive weight. -/
theorem honestStrategy_isSPCC :
    (honestStrategy P).IsSPCC :=
  ⟨honestStrategy_projective P, (fun x => honestMeasurement_isConsistentOn P x.1 x.2),
    honestMeasurement_commuting P⟩

include hxy in
/-- On every question pair of positive weight for the Pauli question sampler the
honest measurement family assigns the zero operator product to every rejected
answer pair.  This is the operator form of perfect acceptance in
`lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1383-1421`. -/
theorem honestMeasurement_rejected_mul (hrej : pauliWinPredicate P x y a b = false) :
    (honestMeasurement x.1 x.2).effect a *
      (honestMeasurement y.1 y.2).effect b = 0 := by
  classical
  obtain ⟨z, hedge, hx, hy⟩ := pauliQuestionDistribution_pos_incidence hxy
  obtain ⟨t₁, x₁⟩ := x
  obtain ⟨t₂, x₂⟩ := y
  dsimp only at hx hy hedge ⊢
  subst hx
  subst hy
  rcases pauliEdges_cases hedge with heq | ⟨s₁, s₂, hs₁, hs₂, hms⟩ | hor | hor
  · rw [heq] at hrej ⊢
    rcases (Bool.eq_false_or_eq_true
      (validPauliAnswer t₂ a)).symm with hva | hva
    · simp [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva]
    refine DistanceCalculus.projective_effect_mul_effect_eq_zero _
      (honestMeasurement_projective P t₂ _) ?_
    rintro rfl
    rw [show pauliWinPredicate P (t₂, pauliCL P t₂ z) (t₂, pauliCL P t₂ z) a a
        = true from by simp [pauliWinPredicate, hva]] at hrej
    exact Bool.noConfusion hrej
  · subst hs₁
    subst hs₂
    solve_by_elim [honest_ms_rejected_mul]
  · solve_by_elim [honest_oriented_rejected_mul]
  · rw [← (honestMeasurement_commute_of_oriented P hor z b a).eq]
    apply honest_oriented_rejected_mul <;> try assumption
    rw [pauliWinPredicate_symm]
    exact hrej

/-- `lem:pauli-completeness`: every admissible Pauli basis test has a
value-one SPCC strategy. Blueprint `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1229-1421`. -/
theorem exists_spcc_value_one :
    ∃ S : SymmetricStrategy (pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  classical
  refine ⟨honestStrategy P, honestStrategy_isSPCC P, ?_⟩
  have hborn : ∀ x y : PauliQuestion P,
      0 < (pauliQuestionDistribution P).weight (x, y) →
      ∀ a b : PauliAnswer P, pauliWinPredicate P x y a b = false →
        outcomeWeight (honestStrategy P).toStrategy x y a b = 0 := by
    intro x y hxy a b hrej
    have hzero := heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero
      _
      _
      (honestMeasurement_effect_transpose P y.1 y.2 b) (honestMeasurement_rejected_mul P x y hxy a b hrej)
    change (inner ℂ (eprState (HonestIndex P))
      (applyOperatorToState
        (heteroKron ((honestMeasurement x.1 x.2).effect a)
          ((honestMeasurement y.1 y.2).effect b))
        (eprState (HonestIndex P)))).re = 0
    rw [applyOperatorToState, Matrix.toLpLin_apply, hzero]
    simp
  have hone : ∀ x y : PauliQuestion P,
      0 < (pauliQuestionDistribution P).weight (x, y) →
      (∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
        if pauliWinPredicate P x y a b then
          outcomeWeight (honestStrategy P).toStrategy x y a b else 0) = 1 := by
    intro x y hxy
    have hcong : (∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
        if pauliWinPredicate P x y a b then
          outcomeWeight (honestStrategy P).toStrategy x y a b else 0) =
        ∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
          outcomeWeight (honestStrategy P).toStrategy x y a b := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : pauliWinPredicate P x y a b = true
      · simp [hab]
      · have hab' := Bool.eq_false_of_not_eq_true hab
        rw [hborn x y hxy a b hab']
        simp
    rw [hcong]
    exact outcomeWeight_sum_eq_one (honestStrategy P).toStrategy x y
  change avgOver (pauliQuestionDistribution P) (fun xy =>
    ∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
      if pauliWinPredicate P xy.1 xy.2 a b then
        outcomeWeight (honestStrategy P).toStrategy xy.1 xy.2 a b else 0) = 1
  have hcongr : avgOver (pauliQuestionDistribution P) (fun xy =>
      ∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
        if pauliWinPredicate P xy.1 xy.2 a b then
          outcomeWeight (honestStrategy P).toStrategy xy.1 xy.2 a b else 0) =
      avgOver (pauliQuestionDistribution P) (fun _ => 1) := by
    simp only [avgOver]
    congr 1 with xy
    rcases lt_or_eq_of_le ((pauliQuestionDistribution P).nonnegative xy) with hpos | hzero
    · simp [*]
    · simp [← hzero]
  rw [hcongr]
  exact avgOver_const_of_isProbability _ (pauliBasisTestSymm P).μ_prob 1

end

end MIPStarRE.QPBT
