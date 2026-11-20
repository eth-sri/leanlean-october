module

public import QPBT.Games.StrategyClasses
public import QPBT.Games.TypedCondLinear
public import QPBT.Test.Completeness.Commutation
public import QPBT.Test.Completeness.HonestStrategy
public import QPBT.Test.Completeness.HonestStrategy.MeasurementFamily
public import QPBT.Test.Completeness.Rejection
public import QPBT.Test.LowDegreeGameMeasurements
public import QPBT.Algebra.Pauli
public import QPBT.Test.MagicSquareTheorems.Basic
public import QPBT.Test.MagicSquareTheorems.PerfectStrategy
public import QPBT.Test.MagicSquareTheorems.Rigidity.Relations
public import QPBT.Test.MagicSquareTheorems.Rigidity.Dilation
public import QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
public import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
public import QPBT.Test.MagicSquareTheorems.Rigidity.Consistency
public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice
public import QPBT.Test.MagicSquareTheorems.Rigidity.Marginals
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

/-- The honest strategy of `lem:pauli-completeness`: the total honest
measurement family of `MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily`
on the maximally entangled state of the Pauli register tensored with the Magic
Square qubit.  Blueprint `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1237-1360`. -/
noncomputable def honestStrategy (P : AdmissibleParams) :
    SymmetricStrategy (pauliBasisTestSymm P) where
  ι := HonestIndex P
  ψ := eprState (HonestIndex P)
  ψ_norm := eprState_norm (HonestIndex P)
  ψ_swap := reindexState_prodComm_eprState (HonestIndex P)
  M := fun q => honestMeasurement P q.1 q.2

/-- Every measurement of the honest strategy is projective. -/
theorem honestStrategy_projective (P : AdmissibleParams) (x : PauliQuestion P) :
    MIPStarRE.QPBT.Measurement.IsProjective ((honestStrategy P).M x) :=
  honestMeasurement_projective P x.1 x.2

/-- The honest strategy is consistent on its maximally entangled state. -/
theorem honestStrategy_isConsistent (P : AdmissibleParams) :
    (honestStrategy P).IsConsistent :=
  fun x => honestMeasurement_isConsistentOn P x.1 x.2

/-- The honest strategy is a symmetric projective consistent commuting
strategy: every measurement is projective, the family is consistent on the
maximally entangled state, and the effects commute on every question pair of
positive weight. -/
theorem honestStrategy_isSPCC (P : AdmissibleParams) :
    (honestStrategy P).IsSPCC :=
  ⟨honestStrategy_projective P, honestStrategy_isConsistent P,
    honestMeasurement_commuting P⟩

/-- On every question pair of positive weight for the Pauli question sampler the
honest measurement family assigns the zero operator product to every rejected
answer pair.  This is the operator form of perfect acceptance in
`lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1383-1421`. -/
theorem honestMeasurement_rejected_mul (P : AdmissibleParams)
    (x y : PauliQuestion P) (hxy : 0 < (pauliQuestionDistribution P).weight (x, y))
    (a b : PauliAnswer P) (hrej : pauliWinPredicate P x y a b = false) :
    (honestMeasurement P x.1 x.2).effect a *
      (honestMeasurement P y.1 y.2).effect b = 0 := by
  classical
  obtain ⟨z, hedge, hx, hy⟩ := pauliQuestionDistribution_pos_incidence P x y hxy
  obtain ⟨t₁, x₁⟩ := x
  obtain ⟨t₂, x₂⟩ := y
  dsimp only at hx hy hedge ⊢
  subst hx
  subst hy
  rcases pauliEdges_cases hedge with heq | ⟨s₁, s₂, hs₁, hs₂, hms⟩ | hor | hor
  · rw [heq] at hrej ⊢
    rcases (Bool.eq_false_or_eq_true
      (validPauliAnswer (P := P) t₂ a)).symm with hva | hva
    · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
    have hab : a ≠ b := by
      rintro rfl
      rw [show pauliWinPredicate P (t₂, pauliCL P t₂ z) (t₂, pauliCL P t₂ z) a a
          = true from by simp [pauliWinPredicate, hva]] at hrej
      exact Bool.noConfusion hrej
    exact DistanceCalculus.projective_effect_mul_effect_eq_zero _
      (honestMeasurement_projective P t₂ _) hab
  · subst hs₁
    subst hs₂
    exact honest_ms_rejected_mul P z hms a b hrej
  · exact honest_oriented_rejected_mul P hor z a b hrej
  · rw [← (honestMeasurement_commute_of_oriented P hor z b a).eq]
    refine honest_oriented_rejected_mul P hor z b a ?_
    rw [pauliWinPredicate_symm]
    exact hrej

/-- `lem:pauli-completeness`: every admissible Pauli basis test has a
value-one SPCC strategy. Blueprint `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1229-1421`. -/
theorem exists_spcc_value_one (P : AdmissibleParams) :
    ∃ S : SymmetricStrategy (pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  classical
  refine ⟨honestStrategy P, honestStrategy_isSPCC P, ?_⟩
  apply Strategy.value_eq_one_of
  intro x y hxy a b hrej
  change DistanceCalculus.stateQForm (eprState (HonestIndex P))
    (heteroKron ((honestMeasurement P x.1 x.2).effect a)
      ((honestMeasurement P y.1 y.2).effect b)) = 0
  rw [stateQForm_eprState_heteroKron _ _ (honestMeasurement_effect_transpose P y.1 y.2 b),
    honestMeasurement_rejected_mul P x y hxy a b hrej]
  simp [heteroKron, DistanceCalculus.stateQForm, applyOperatorToState]

end

end MIPStarRE.QPBT
