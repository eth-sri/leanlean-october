module

public import MIPStarRE.Quantum.Measurement
public import MIPStarRE.LDT.Basic.DistributionAvg
public import MIPStarRE.LDT.Basic.Distribution

/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are blueprint `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

/--
A finite two-player one-round game with a probability distribution on question
pairs and a Boolean decision predicate.  This is blueprint
`def:game`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-24`.
-/
structure Game where
  QuestionA : Type
  QuestionB : Type
  AnswerA : Type
  AnswerB : Type
  [questionAFintype : Fintype QuestionA]
  [questionBFintype : Fintype QuestionB]
  [answerAFintype : Fintype AnswerA]
  [answerBFintype : Fintype AnswerB]
  [questionADecidableEq : DecidableEq QuestionA]
  [questionBDecidableEq : DecidableEq QuestionB]
  [answerADecidableEq : DecidableEq AnswerA]
  [answerBDecidableEq : DecidableEq AnswerB]
  μ : Distribution (QuestionA × QuestionB)
  μ_prob : μ.IsProbability
  decide : QuestionA → QuestionB → AnswerA → AnswerB → Bool

attribute [instance] Game.questionAFintype Game.questionBFintype
  Game.answerAFintype Game.answerBFintype Game.questionADecidableEq
  Game.questionBDecidableEq Game.answerADecidableEq Game.answerBDecidableEq

/-- Projectivity of every effect in a POVM (blueprint
`def:povm-conventions`; paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:68-72`). -/
def Measurement.IsProjective {α d : Type*} [Fintype α] [Fintype d] [DecidableEq d]
    (M : Measurement α d) : Prop :=
  ∀ a, IsProj (M.effect a)

/--
The tensor-product strategy of blueprint
`def:tensor-product-strategy` (paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`).
-/
structure Strategy (G : Game) where
  ιA : Type
  ιB : Type
  [ιAFintype : Fintype ιA]
  [ιBFintype : Fintype ιB]
  [ιADecidableEq : DecidableEq ιA]
  [ιBDecidableEq : DecidableEq ιB]
  ψ : EuclideanSpace ℂ (ιA × ιB)
  ψ_norm : ‖ψ‖ = 1
  A : G.QuestionA → Measurement G.AnswerA ιA
  B : G.QuestionB → Measurement G.AnswerB ιB

attribute [instance] Strategy.ιAFintype Strategy.ιBFintype
  Strategy.ιADecidableEq Strategy.ιBDecidableEq

/-- The rectangular tensor placement used in strategy probabilities.  This is
the finite-matrix realization of blueprint
`def:tensor-product-strategy`; paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`.
-/
def heteroKron {ιA ιB : Type*} (A : Op ιA) (B : Op ιB) : Op (ιA × ιB) :=
  Matrix.kronecker A B

/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/

section

variable {ι κ : Type*}
include ι κ

theorem heteroKron_conjTranspose (A : Op ι) (B : Op κ) :
    (heteroKron A B)ᴴ = heteroKron Aᴴ Bᴴ := Matrix.conjTranspose_kronecker A B

theorem heteroKron_zero_left (B : Op κ) :
    heteroKron (0 : Op ι) B = 0 := Matrix.zero_kronecker B

theorem heteroKron_zero_right (A : Op ι) :
    heteroKron A (0 : Op κ) = 0 := Matrix.kronecker_zero A

theorem heteroKron_smul_left {R : Type*} [SMul R ℂ]
    [IsScalarTower R ℂ ℂ] (c : R) (A : Op ι) (B : Op κ) :
    heteroKron (c • A) B = c • heteroKron A B := Matrix.smul_kronecker c A B

theorem heteroKron_smul_right {R : Type*} [SMul R ℂ]
    [SMulCommClass R ℂ ℂ] (c : R) (A : Op ι) (B : Op κ) :
    heteroKron A (c • B) = c • heteroKron A B := Matrix.kronecker_smul c A B

end

section

variable {ιA ιB : Type*}
include ιA ιB

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`): the tensor
placement is multiplicative, `(A ⊗ C) * (B ⊗ D) = (A * B) ⊗ (C * D)`. -/
theorem heteroKron_mul [Fintype ιA] [Fintype ιB]
    (A B : Op ιA) (C D : Op ιB) :
    heteroKron A C * heteroKron B D = heteroKron (A * B) (C * D) := by
  unfold heteroKron Matrix.kronecker
  exact Eq.symm (Matrix.mul_kronecker_mul A B C D)

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): the tensor
placement of the two identity operators is the identity operator on the product
space. -/
theorem heteroKron_one_one [DecidableEq ιA] [DecidableEq ιB] :
    heteroKron (1 : Op ιA) (1 : Op ιB) = 1 := by
  unfold heteroKron Matrix.kronecker
  simp

section

variable (A : Op ιA)
include A

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects negation in the left factor. -/
theorem heteroKron_neg_left (C : Op ιB) :
    heteroKron (-A) C = -heteroKron A C := by
  ext p q
  simp [heteroKron]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects negation in the right factor. -/
theorem heteroKron_neg_right (C : Op ιB) :
    heteroKron A (-C) = -heteroKron A C := by
  ext p q
  simp [heteroKron]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
is additive in the left factor. -/
theorem heteroKron_add_left (B : Op ιA) (C : Op ιB) :
    heteroKron (A + B) C = heteroKron A C + heteroKron B C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, add_mul]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
is additive in the right factor. -/
theorem heteroKron_add_right (B C : Op ιB) :
    heteroKron A (B + C) = heteroKron A B + heteroKron A C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, mul_add]

end

end

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`: the
tensor placement of possibly rectangular matrices respects differences in the
left factor.  This is the general form of `heteroKron_sub_left` below, needed
where the left factor is the matrix of an isometry between distinct index
types (blueprint
`thm:ms-rigidity`). -/
theorem kroneckerMap_sub_left {m n p q : Type*} (A B : Matrix m n ℂ) (C : Matrix p q ℂ) :
    Matrix.kroneckerMap (· * ·) (A - B) C =
      Matrix.kroneckerMap (· * ·) A C - Matrix.kroneckerMap (· * ·) B C := by
  ext p' q'
  simp [sub_mul]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`: the
tensor placement of possibly rectangular matrices respects differences in the
right factor.  This is the general form of `heteroKron_sub_right` below. -/
theorem kroneckerMap_sub_right {m n p q : Type*} (A : Matrix m n ℂ) (B C : Matrix p q ℂ) :
    Matrix.kroneckerMap (· * ·) A (B - C) =
      Matrix.kroneckerMap (· * ·) A B - Matrix.kroneckerMap (· * ·) A C := by
  ext p' q'
  simp [mul_sub]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the left factor. -/
theorem heteroKron_sub_left {ιA ιB : Type*} (A B : Op ιA) (C : Op ιB) :
    heteroKron (A - B) C = heteroKron A C - heteroKron B C :=
  kroneckerMap_sub_left A B C

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the right factor. -/
theorem heteroKron_sub_right {ιA ιB : Type*} (A : Op ιA) (B C : Op ιB) :
    heteroKron A (B - C) = heteroKron A B - heteroKron A C :=
  kroneckerMap_sub_right A B C

/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
include ι

/-- Apply a finite matrix to a Euclidean-space state.  This is the Hilbert-space
action underlying `def:tensor-product-value`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`. -/
noncomputable def applyOperatorToState
    (M : Op ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin M ψ

theorem applyOperatorToState_one
    (v : EuclideanSpace ℂ ι) : applyOperatorToState (1 : Op ι) v = v := by
  simp [applyOperatorToState]

theorem applyOperatorToState_smul_op
    (c : ℂ) (M : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (c • M) v = c • applyOperatorToState M v := by
  simp [applyOperatorToState]

end

namespace DistanceCalculus

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι)
include ι ψ

/-- Formalization-only definition for the agreement facts (Facts 4.13 and 4.14):
the real quadratic form of an operator evaluated in a state vector. -/
noncomputable def stateQForm (M : Op ι) : ℝ :=
  (inner ℂ ψ (applyOperatorToState M ψ)).re

theorem stateQForm_zero : stateQForm ψ (0 : Op ι) = 0 := by
  simp [stateQForm, applyOperatorToState]

end

/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → Op ι) :
    stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, stateQForm ψ (M b) := by
  simp [stateQForm, applyOperatorToState]

/-- Tensor placement is additive over finite sums in the left factor. This is
the formalization-only identity `lem:distance-tensor-sum-left`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem heteroKron_finset_sum_left {β ιA ιB : Type*} (s : Finset β)
    (A : β → Op ιA) (C : Op ιB) :
    heteroKron (∑ b ∈ s, A b) C = ∑ b ∈ s, heteroKron (A b) C := by
  ext p q
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Finset.sum_mul]

/-- Tensor placement is additive over finite sums in the right factor. This is
the formalization-only identity `lem:distance-tensor-sum-right`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem heteroKron_finset_sum_right {β ιA ιB : Type*} (s : Finset β)
    (A : Op ιA) (C : β → Op ιB) :
    heteroKron A (∑ b ∈ s, C b) = ∑ b ∈ s, heteroKron A (C b) := by
  ext p q
  simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Finset.mul_sum]

end DistanceCalculus

section

variable {G : Game} (S : Strategy G)
include G S

section

variable (x : G.QuestionA)

/-- The Born weight of an answer pair for a strategy.  Lean-only support for
blueprint `def:tensor-product-value`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-48`. -/
noncomputable def outcomeWeight (y : G.QuestionB) (a : G.AnswerA) (b : G.AnswerB) : ℝ :=
  let M : MIPStarRE.Quantum.Op (S.ιA × S.ιB) :=
    heteroKron ((S.A x).effect a) ((S.B y).effect b)
  let acted := applyOperatorToState M S.ψ
  (inner ℂ S.ψ acted).re

/-- Alice's marginal Born weight for an answer at a fixed question. -/
noncomputable def aliceOutcomeWeight (a : G.AnswerA) : ℝ :=
  let M : MIPStarRE.Quantum.Op (S.ιA × S.ιB) :=
    heteroKron ((S.A x).effect a) 1
  (inner ℂ S.ψ (applyOperatorToState M S.ψ)).re

/-- Bob's marginal Born weight for an answer at a fixed question. -/
noncomputable def bobOutcomeWeight
    (y : G.QuestionB) (b : G.AnswerB) : ℝ :=
  let M : MIPStarRE.Quantum.Op (S.ιA × S.ιB) :=
    heteroKron 1 ((S.B y).effect b)
  (inner ℂ S.ψ (applyOperatorToState M S.ψ)).re

/-- The Born weight of a decidable event on the two answers at fixed questions. -/
noncomputable def outcomeEventWeight (y : G.QuestionB)
    (E : G.AnswerA → G.AnswerB → Prop) [DecidableRel E] : ℝ :=
  ∑ a : G.AnswerA, ∑ b : G.AnswerB,
    if E a b then outcomeWeight S x y a b else 0

/-- The marginal Born weight of a decidable event on Alice's answer. -/
noncomputable def aliceEventWeight (E : G.AnswerA → Prop) [DecidablePred E] : ℝ :=
  ∑ a : G.AnswerA, if E a then aliceOutcomeWeight S x a else 0

end

/-- The marginal Born weight of a decidable event on Bob's answer. -/
noncomputable def bobEventWeight
    (y : G.QuestionB) (E : G.AnswerB → Prop) [DecidablePred E] : ℝ :=
  ∑ b : G.AnswerB, if E b then bobOutcomeWeight S y b else 0

end

section

variable {G : Game} (S : Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
include G S x y

/-- Every answer-pair Born weight is nonnegative.  This is formalization-only
support for the probability expression in `def:tensor-product-value`. -/
theorem outcomeWeight_nonneg (a : G.AnswerA) (b : G.AnswerB) :
    0 ≤ outcomeWeight S x y a b := by
  unfold outcomeWeight applyOperatorToState heteroKron
  exact
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (Matrix.nonneg_iff_posSemidef.mp
        (kronecker_nonneg ((S.A x).pos a) ((S.B y).pos b)))).re_inner_nonneg_right S.ψ

open DistanceCalculus in
/-- Summing over Bob's answers gives Alice's marginal Born weight. -/
theorem sum_outcome_weight_right (a : G.AnswerA) :
    (∑ b : G.AnswerB, outcomeWeight S x y a b) = aliceOutcomeWeight S x a := by
  change (∑ b, stateQForm S.ψ (heteroKron ((S.A x).effect a) ((S.B y).effect b))) = _
  rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, (S.B y).sum_eq_one]
  rfl

open DistanceCalculus in
/-- Summing over Alice's answers gives Bob's marginal Born weight. -/
theorem sum_outcome_weight_left (b : G.AnswerB) :
    (∑ a : G.AnswerA, outcomeWeight S x y a b) = bobOutcomeWeight S y b := by
  change (∑ a, stateQForm S.ψ (heteroKron ((S.A x).effect a) ((S.B y).effect b))) = _
  rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_left, (S.A x).sum_eq_one]
  rfl

open DistanceCalculus in
/-- The Born weights of all answer pairs at fixed questions sum to one. -/
theorem outcomeWeight_sum_eq_one :
    ∑ a : G.AnswerA, ∑ b : G.AnswerB, outcomeWeight S x y a b = 1 := by
  simp_rw [sum_outcome_weight_right]
  change (∑ a, stateQForm S.ψ (heteroKron ((S.A x).effect a) 1)) = 1
  rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_left, (S.A x).sum_eq_one,
    heteroKron_one_one]
  simp [stateQForm, applyOperatorToState, S.ψ_norm]

/-- Every answer event has nonnegative Born weight. -/
theorem outcome_event_weight_nonneg
    (E : G.AnswerA → G.AnswerB → Prop) [DecidableRel E] :
    0 ≤ outcomeEventWeight S x y E := by
  unfold outcomeEventWeight
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact outcomeWeight_nonneg S x y a b
    · rfl

/-- An answer event depending only on Alice has its Alice marginal weight. -/
theorem outcome_event_weight_left_eq
    (E : G.AnswerA → Prop) [DecidablePred E] :
    outcomeEventWeight S x y (fun a _ => E a) = aliceEventWeight S x E := by
  unfold outcomeEventWeight aliceEventWeight
  apply Finset.sum_congr rfl
  intro a _
  simp_all [sum_outcome_weight_right S x y a]

/-- An answer event depending only on Bob has its Bob marginal weight. -/
theorem outcome_event_weight_right_eq
    (E : G.AnswerB → Prop) [DecidablePred E] :
    outcomeEventWeight S x y (fun _ b => E b) = bobEventWeight S y E := by
  unfold outcomeEventWeight bobEventWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp_all [sum_outcome_weight_left S x y b]

/-- Inclusion of answer events implies the corresponding Born-weight inequality. -/
theorem outcome_event_weight_mono
    (E F : G.AnswerA → G.AnswerB → Prop) [DecidableRel E] [DecidableRel F]
    (hEF : ∀ a b, E a b → F a b) :
    outcomeEventWeight S x y E ≤ outcomeEventWeight S x y F := by
  unfold outcomeEventWeight
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases hE : E a b
  · simp_all
  · simp [hE, ↓reduceIte]
    split_ifs
    · exact outcomeWeight_nonneg S x y a b
    · rfl

end

section

variable {G : Game} (S : Strategy G)
include G S

/--
The tensor-product value, expressed as the distribution average of the Born
probabilities.  This is blueprint
`def:tensor-product-value`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-57`.
-/
noncomputable def Strategy.value : ℝ :=
  avgOver G.μ (fun xy =>
    ∑ a : G.AnswerA, ∑ b : G.AnswerB,
      if G.decide xy.1 xy.2 a b then outcomeWeight S xy.1 xy.2 a b else 0)
/-- The average mass of the rejected answer pairs is one minus the strategy
value.  This is formalization-only support for blueprint
`def:tensor-product-value`. -/
theorem rejectionMass_eq_one_sub_value :
    avgOver G.μ (fun questions =>
      ∑ a, ∑ b,
        if G.decide questions.1 questions.2 a b then 0
        else outcomeWeight S questions.1 questions.2 a b) =
      1 - S.value := by
  classical
  unfold Strategy.value
  rw [← avgOver_const_of_isProbability G.μ G.μ_prob 1, ← avgOver_sub]
  refine avgOver_congr _ _ _ fun xy => ?_
  rw [← outcomeWeight_sum_eq_one S xy.1 xy.2]
  simp only [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    split <;> simp

/-- A strategy wins with certainty if rejected outcomes have zero Born weight on weighted questions. -/
theorem Strategy.value_eq_one_of
    (h : ∀ x y, 0 < G.μ.weight (x, y) → ∀ a b, G.decide x y a b = false →
      outcomeWeight S x y a b = 0) : S.value = 1 := by
  symm
  apply sub_eq_zero.mp
  rw [← rejectionMass_eq_one_sub_value S, avgOver]
  refine Finset.sum_eq_zero fun xy _ => ?_
  obtain hp | hz := lt_or_eq_of_le (G.μ.nonnegative xy)
  · simp_all
  · rw [← hz, zero_mul]

/-- Every strategy value is at most one.  Formalization-only support for
blueprint `def:tensor-product-value`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-57`. -/
theorem Strategy.value_le_one : S.value ≤ 1 := by
  have hnn :
      (0 : ℝ) ≤ avgOver G.μ (fun questions =>
        ∑ a, ∑ b,
          if G.decide questions.1 questions.2 a b then 0
          else outcomeWeight S questions.1 questions.2 a b) :=
    avgOver_nonneg _ _ fun questions =>
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
        split_ifs
        · rfl
        · exact outcomeWeight_nonneg S _ _ _ _
  rw [rejectionMass_eq_one_sub_value S] at hnn
  linarith

end

end MIPStarRE.QPBT
