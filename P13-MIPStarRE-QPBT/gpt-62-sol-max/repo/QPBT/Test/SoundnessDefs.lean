module

public import QPBT.Test.PauliBasisTest
public import QPBT.Games.ErrorFunctions
public import QPBT.State

/-!
# Pauli basis test soundness interface

This module contains the quantitative error function and the closed definitions
used to state Pauli basis test soundness.  The carriers are concrete
finite-dimensional vectors and matrices so that the soundness proof can use the
existing Hilbert-space API without introducing a dependency cycle.

## References

The interface supports blueprint
`thm:pauli`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The distance functionals use blueprint `def:state-distance` and
`def:povm-distance`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- The Pauli-test error scale.  The argument order is `(a, b, ε, m, d, q)`;
the powers are real `rpow`s and the asymptotic constants are absorbed into `a`,
as specified by blueprint `thm:pauli`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`).
-/
noncomputable def deltaQld (a b ε : ℝ) (m d q : ℕ) : ℝ :=
  a * Real.rpow ((m * d : ℕ) : ℝ) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

/-- The Pauli-test error specialized to its admissible parameters. -/
abbrev AdmissibleParams.qldError (P : AdmissibleParams) (a b ε : ℝ) :=
  deltaQld a b ε P.m P.d P.q

namespace AdmissibleParams

section

variable (P : AdmissibleParams)
include P

/-- The degree budget and the error-dependent factor in `qldError`. -/
abbrev degreeBudget : ℝ := ((P.m * P.d : ℕ) : ℝ)

abbrev qldTail (b ε : ℝ) : ℝ :=
  ε ^ b + (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * P.degreeBudget))

theorem degreeBudget_ge_one : 1 ≤ P.degreeBudget :=
  Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)

theorem fieldSize_ge_one : (1 : ℝ) ≤ P.q := by
  obtain ⟨n, -, hn⟩ := P.hq
  rw [hn]
  exact_mod_cast Nat.one_le_pow _ _ (by decide)

theorem degreeBudget_le_prefactor {a : ℝ} (ha : 1 ≤ a) :
    P.degreeBudget ≤ a * P.degreeBudget ^ a :=
  size_le_power_prefactor P.degreeBudget_ge_one ha

theorem qldTail_nonneg (b : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ P.qldTail b ε :=
  soundnessTail_nonneg P.q P.degreeBudget b hε

theorem qldTail_le_three {b ε : ℝ}
    (hb : 0 ≤ b) (hε : 0 ≤ ε) (hε' : ε ≤ 1) : P.qldTail b ε ≤ 3 := by
  have hq := Real.rpow_le_one_of_one_le_of_nonpos P.fieldSize_ge_one (neg_nonpos.mpr hb)
  have hdegree : 0 ≤ P.degreeBudget := zero_le_one.trans P.degreeBudget_ge_one
  have ht := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    (neg_nonpos.mpr (mul_nonneg hb hdegree))
  unfold qldTail
  linarith [Real.rpow_le_one hε hε' hb]

end

end AdmissibleParams

section

variable {P : AdmissibleParams} {a b ε : ℝ}
include P a b ε

theorem deltaQld_nonneg (ha : 0 ≤ a) (hε : 0 ≤ ε) :
    0 ≤ P.qldError a b ε :=
  mul_nonneg (mul_nonneg ha (Real.rpow_nonneg (by positivity) _)) (P.qldTail_nonneg b hε)

/-- The error envelope dominates its input-noise term. -/
theorem rpow_noise_le_deltaQld
    (ha : 1 ≤ a) (hε : 0 ≤ ε) : ε ^ b ≤ P.qldError a b ε :=
  (rpow_noise_le_soundnessTail P.q P.degreeBudget b ε).trans
    (le_mul_of_one_le_left (P.qldTail_nonneg b hε)
      (P.degreeBudget_ge_one.trans (P.degreeBudget_le_prefactor ha)))

/-- The degree-to-field-size ratio is one of the errors absorbed by `qldError`. -/
theorem ratio_le_deltaQld
    (ha : 1 ≤ a) (hb : b ≤ 1) (hε : 0 ≤ ε) : P.degreeBudget / P.q ≤ P.qldError a b ε := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one]
  exact mul_le_mul (P.degreeBudget_le_prefactor ha)
    ((Real.rpow_le_rpow_of_exponent_le P.fieldSize_ge_one (neg_le_neg hb)).trans
      (rpow_field_le_soundnessTail P.q P.degreeBudget b hε)) (by positivity)
    (zero_le_one.trans (P.degreeBudget_ge_one.trans (P.degreeBudget_le_prefactor ha)))

/-- Absorb a constant multiplier by increasing the universal prefactor. -/
theorem scale_deltaQld_le {K : ℝ}
    (ha : 1 ≤ a) (hε : 0 ≤ ε) (hK : 1 ≤ K) :
    K * P.qldError a b ε ≤ P.qldError (K * a) b ε := by
  have ha0 := zero_le_one.trans ha
  change K * (a * P.degreeBudget ^ a * P.qldTail b ε) ≤
    K * a * P.degreeBudget ^ (K * a) * P.qldTail b ε
  rw [← mul_assoc, ← mul_assoc]
  have ht := P.qldTail_nonneg b hε
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le P.degreeBudget_ge_one (le_mul_of_one_le_left ha0 hK))
    (mul_nonneg (zero_le_one.trans hK) ha0)) ht

end

/-- Monotonicity obligation for adjusting the universal constants in
`deltaQld` on the source parameter domain. This Lean-only helper supports the
enlargement of `a` and shrinkage of `b` for `0 ≤ ε ≤ 1` recorded in
`rem:pauli-robustness-form` and stated as `lem:delta-qld-mono-support`,
blueprint `ch16_qpbt_extraction.tex`; the source makes this constant adjustment
at `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1402`. It is
not an additional hypothesis of `thm:pauli` or `lem:qld-4-7`. -/
theorem deltaQld_mono {P : AdmissibleParams} {a a' b b' ε : ℝ}
    (ha0 : 1 ≤ a) (ha : a ≤ a') (hb : b' ≤ b) (hb' : 0 < b')
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    P.qldError a b ε ≤ P.qldError a' b' ε := by
  have hd := P.degreeBudget_ge_one
  have hq := P.fieldSize_ge_one
  have ht := P.qldTail_nonneg b hε0
  change a * P.degreeBudget ^ a * P.qldTail b ε ≤ a' * P.degreeBudget ^ a' * P.qldTail b' ε
  have ha' : 0 ≤ a' := by linarith
  have ht' : P.qldTail b ε ≤ P.qldTail b' ε := by
    unfold AdmissibleParams.qldTail
    have h₁ := Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb'.le hb
    have h₂ := Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hb)
    have h₃ := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (neg_le_neg (mul_le_mul_of_nonneg_right hb (zero_le_one.trans hd)))
    linarith
  gcongr

/-- The ideal auxiliary state `aux ⊗ EPR_q^{⊗M}` in the shuffled register
ordering.  The EPR factor is the concrete `eprState` from blueprint
`def:EPR`; paper
`references/qpbt-paper/04_preliminaries.tex:946-955`).
-/
noncomputable def idealState (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (aux : EuclideanSpace ℂ (ιA' × ιB')) :
    EuclideanSpace ℂ ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  (EuclideanSpace.equiv ((ιA' × PauliRegister P) ×
      (ιB' × PauliRegister P)) ℂ).symm
    (fun p =>
      ((EuclideanSpace.equiv (ιA' × ιB') ℂ) aux (p.1.1, p.2.1)) *
        ((EuclideanSpace.equiv (PauliRegister P × PauliRegister P) ℂ)
          (eprState (PauliRegister P)) (p.1.2, p.2.2)))

/-- The A-side ideal Pauli projector, with identities on the auxiliary and
B-side registers.  This is a concrete matrix form of the operator comparison
in blueprint `thm:pauli`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`).
-/
noncomputable def pauliProjOnA'' (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind)
    (u : PauliRegister P) :
    Op ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  heteroKron (heteroKron 1 (pauliProj W u)) 1

/-- The symmetric B-side ideal Pauli projector from blueprint
`thm:pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
noncomputable def pauliProjOnB'' (P : AdmissibleParams)
    {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind)
    (u : PauliRegister P) :
    Op ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  heteroKron 1 (heteroKron 1 (pauliProj W u))

section

variable {P : AdmissibleParams} {G : Game}
    (S : Strategy G)
include P G S

/-- Lift a conjugated A-side effect to the full ideal register in blueprint
`thm:pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
noncomputable def liftedAEffect {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P))
    (M : Op S.ιA) :
    Op ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  heteroKron (conjIsometry φA M) 1

/-- Lift a conjugated B-side effect to the full ideal register in blueprint
`thm:pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
noncomputable def liftedBEffect {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P))
    (M : Op S.ιB) :
    Op ((ιA' × PauliRegister P) × (ιB' × PauliRegister P)) :=
  heteroKron 1 (conjIsometry φB M)

end

/-- A finite witness packaging the auxiliary dimensions, isometries, and state
from `thm:pauli`.  This structure is a Lean-only encoding of the existential
data in the paper theorem; it introduces no extra hypothesis.  Blueprint
`thm:pauli`, paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/
structure PauliSoundnessWitness (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) where
  ιA' : Type
  ιB' : Type
  [ιAFintype : Fintype ιA']
  [ιBFintype : Fintype ιB']
  [ιADecidableEq : DecidableEq ιA']
  [ιBDecidableEq : DecidableEq ιB']
  φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
    EuclideanSpace ℂ (ιA' × PauliRegister P)
  φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
    EuclideanSpace ℂ (ιB' × PauliRegister P)
  aux : EuclideanSpace ℂ (ιA' × ιB')
  aux_norm : ‖aux‖ = 1

attribute [instance] PauliSoundnessWitness.ιAFintype PauliSoundnessWitness.ιBFintype
  PauliSoundnessWitness.ιADecidableEq PauliSoundnessWitness.ιBDecidableEq

section

variable (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind)
include P S w W

/-- The A-side operator distance for the completed Pauli family obtained by
folding every wrong-form answer into outcome zero. This Lean-only quantity is
used internally by the extraction and Naimark transfer; the source-facing
distance is `rawPauliOperatorDistanceA`. -/
noncomputable def pauliOperatorDistanceA : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedAEffect S w.φA
        (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect u) -
      pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2

/-- The symmetric B-side operator distance for the completed Pauli family.
This is internal support for the extraction proof; the source-facing distance
is `rawPauliOperatorDistanceB`. -/
noncomputable def pauliOperatorDistanceB : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedBEffect S w.φB
        (((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect u) -
      pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2

/-- Alice's source-facing Pauli operator distance. The strategy effect is the
raw effect of the prescribed answer `.pauliOutcome u`, exactly as in
`thm:pauli`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1438-1443`.
The sum is the finite realization of blueprint `def:povm-distance`. -/
noncomputable def rawPauliOperatorDistanceA : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedAEffect S w.φA
        ((S.A (pauliQuestion P W)).effect (.pauliOutcome u)) -
      pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2

/-- Bob's source-facing Pauli operator distance, using the raw prescribed
answer effect from `thm:pauli`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1438-1443`.
-/
noncomputable def rawPauliOperatorDistanceB : ℝ :=
  ∑ u : PauliRegister P,
      ‖applyOperatorToState (liftedBEffect S w.φB
        ((S.B (pauliQuestion P W)).effect (.pauliOutcome u)) -
      pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2

end

section

variable {P : AdmissibleParams} {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P S)
include P S w

/-- A witness meets the error tolerance for the state and both operator families. -/
abbrev PauliSoundnessWitness.within (A B : PauliKind → ℝ) (error : ℝ) : Prop :=
  ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ error ∧
    (∀ W, A W ≤ error) ∧ (∀ W, B W ≤ error)

abbrev PauliSoundnessWitness.completedWithin :=
  w.within (pauliOperatorDistanceA P S w) (pauliOperatorDistanceB P S w)

abbrev PauliSoundnessWitness.rawWithin :=
  w.within (rawPauliOperatorDistanceA P S w) (rawPauliOperatorDistanceB P S w)

end

end

end MIPStarRE.QPBT
