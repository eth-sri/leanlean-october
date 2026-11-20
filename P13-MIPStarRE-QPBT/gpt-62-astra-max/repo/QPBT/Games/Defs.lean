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

open scoped MatrixOrder ComplexOrder in
/-- Effects are Hermitian because they are positive semidefinite. -/
theorem measurement_effect_hermitian {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι) (a : α) : (M.effect a)ᴴ = M.effect a :=
  (Matrix.nonneg_iff_posSemidef.mp (M.pos a)).isHermitian

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

section

variable {m ιA n ιB p : Type*} (A : Op ιA) (B C : Op ιB) {q : Type*}

/-- The rectangular tensor placement used in strategy probabilities.  This is
the finite-matrix realization of blueprint
`def:tensor-product-strategy`; paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`.
-/
def heteroKron : Op (ιA × ιB) :=
  Matrix.kronecker A B

/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/

theorem heteroKron_conjTranspose (A : Op ιA) (B : Op ιB) :
    (heteroKron A B)ᴴ = heteroKron Aᴴ Bᴴ := Matrix.conjTranspose_kronecker _ _

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26-38`): the tensor
placement is multiplicative, `(A ⊗ C) * (B ⊗ D) = (A * B) ⊗ (C * D)`. -/
theorem heteroKron_mul [Fintype ιA] [Fintype ιB]
    (A B : Op ιA) (C D : Op ιB) :
    heteroKron A C * heteroKron B D = heteroKron (A * B) (C * D) := Eq.symm (Matrix.mul_kronecker_mul A B C D)

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): the tensor
placement of the two identity operators is the identity operator on the product
space. -/
theorem heteroKron_one_one [DecidableEq ιA] [DecidableEq ιB] :
    heteroKron (1 : Op ιA) (1 : Op ιB) = 1 := by
  exact Matrix.one_kronecker_one

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects negation in the left factor. -/
theorem heteroKron_neg_left :
    heteroKron (-A) C = -heteroKron A C := by
  ext p q
  simp [heteroKron]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects negation in the right factor. -/
theorem heteroKron_neg_right :
    heteroKron A (-C) = -heteroKron A C := by
  ext p q
  simp [heteroKron]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
is additive in the left factor. -/
theorem heteroKron_add_left (A B : Op ιA) (C : Op ιB) :
    heteroKron (A + B) C = heteroKron A C + heteroKron B C := by
  ext p q
  simp [heteroKron, add_mul]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
is additive in the right factor. -/
theorem heteroKron_add_right :
    heteroKron A (B + C) = heteroKron A B + heteroKron A C := by
  ext p q
  simp [heteroKron, mul_add]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`: the
tensor placement of possibly rectangular matrices respects differences in the
left factor.  This is the general form of `heteroKron_sub_left` below, needed
where the left factor is the matrix of an isometry between distinct index
types (blueprint
`thm:ms-rigidity`). -/
theorem kroneckerMap_sub_left (A B : Matrix m n ℂ) (C : Matrix p q ℂ) :
    Matrix.kroneckerMap (· * ·) (A - B) C =
      Matrix.kroneckerMap (· * ·) A C - Matrix.kroneckerMap (· * ·) B C := by
  ext p' q'
  simp [sub_mul]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`: the
tensor placement of possibly rectangular matrices respects differences in the
right factor.  This is the general form of `heteroKron_sub_right` below. -/
theorem kroneckerMap_sub_right (A : Matrix m n ℂ) (B C : Matrix p q ℂ) :
    Matrix.kroneckerMap (· * ·) A (B - C) =
      Matrix.kroneckerMap (· * ·) A B - Matrix.kroneckerMap (· * ·) A C := by
  ext p' q'
  simp [mul_sub]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the left factor. -/
theorem heteroKron_sub_left (A B : Op ιA) (C : Op ιB) :
    heteroKron (A - B) C = heteroKron A C - heteroKron B C :=
  kroneckerMap_sub_left A B C

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the right factor. -/
theorem heteroKron_sub_right :
    heteroKron A (B - C) = heteroKron A B - heteroKron A C :=
  kroneckerMap_sub_right A B C

end

/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/
/-- Apply a finite matrix to a Euclidean-space state.  This is the Hilbert-space
action underlying `def:tensor-product-value`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`. -/
noncomputable def applyOperatorToState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Op ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin M ψ

section

variable {G : Game} (S : Strategy G) (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA)
  (b : G.AnswerB) (E F : G.AnswerA → G.AnswerB → Prop) [DecidableRel E]

/-- The Born weight of an answer pair for a strategy.  Lean-only support for
blueprint `def:tensor-product-value`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-48`. -/
noncomputable def outcomeWeight : ℝ :=
  let M :=
    heteroKron ((S.A x).effect a) ((S.B y).effect b)
  let acted := applyOperatorToState M S.ψ
  (inner ℂ S.ψ acted).re

/-- Alice's marginal Born weight for an answer at a fixed question. -/
noncomputable def aliceOutcomeWeight : ℝ :=
  let M :=
    heteroKron ((S.A x).effect a) 1
  (inner ℂ S.ψ (applyOperatorToState M S.ψ)).re

/-- The Born weight of a decidable event on the two answers at fixed questions. -/
noncomputable def outcomeEventWeight : ℝ :=
  ∑ a : G.AnswerA, ∑ b : G.AnswerB,
    if E a b then outcomeWeight S x y a b else 0

/-- The marginal Born weight of a decidable event on Alice's answer. -/
noncomputable def aliceEventWeight (E : G.AnswerA → Prop) [DecidablePred E] : ℝ :=
  ∑ a : G.AnswerA, if E a then aliceOutcomeWeight S x a else 0

/-- Every answer-pair Born weight is nonnegative.  This is formalization-only
support for the probability expression in `def:tensor-product-value`. -/
theorem outcomeWeight_nonneg :
    0 ≤ outcomeWeight S x y a b := by
  exact
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (Matrix.nonneg_iff_posSemidef.mp
        (kronecker_nonneg ((S.A x).pos a) ((S.B y).pos b)))).re_inner_nonneg_right S.ψ

/-- The Born weights of all answer pairs at fixed questions sum to one.  This
is formalization-only support for the POVM normalization implicit in
`def:tensor-product-value`. -/
theorem outcomeWeight_sum_eq_one :
    ∑ a : G.AnswerA, ∑ b : G.AnswerB, outcomeWeight S x y a b = 1 := by
  have hsum :
      (∑ a : G.AnswerA, ∑ b : G.AnswerB,
        heteroKron ((S.A x).effect a) ((S.B y).effect b)) =
          1 := by
    ext i j
    simp [Matrix.sum_apply, heteroKron, Matrix.kroneckerMap_apply]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [show (∑ a : G.AnswerA, (S.A x).effect a i.1 j.1) =
        _ by
      simpa only [Matrix.sum_apply] using congrFun (congrFun (S.A x).sum_eq_one i.1) j.1]
    rw [show (∑ b : G.AnswerB, (S.B y).effect b i.2 j.2) =
        _ by
      simpa only [Matrix.sum_apply] using congrFun (congrFun (S.B y).sum_eq_one i.2) j.2]
    exact congrFun (congrFun
      (Matrix.one_kronecker_one) i) j
  calc
    _ =
        (inner ℂ S.ψ
          (applyOperatorToState
            (∑ a : G.AnswerA, ∑ b : G.AnswerB,
              heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re := by
          simp [outcomeWeight, applyOperatorToState]
    _ = (inner ℂ S.ψ (applyOperatorToState 1 S.ψ)).re := by rw [hsum]
    _ = 1 := by
      simp [applyOperatorToState, S.ψ_norm]

/-- Summing over Bob's answers gives Alice's marginal Born weight. -/
theorem sum_outcome_weight_right :
    (∑ b : G.AnswerB, outcomeWeight S x y a b) = aliceOutcomeWeight S x a := by
  have hsum :
      (∑ b : G.AnswerB, heteroKron ((S.A x).effect a) ((S.B y).effect b)) =
        heteroKron ((S.A x).effect a) 1 := by
    ext i j
    simp [Matrix.sum_apply, heteroKron, Matrix.kroneckerMap_apply]
    rw [← Finset.mul_sum]
    rw [show (∑ b : G.AnswerB, (S.B y).effect b i.2 j.2) =
        _ by
      simpa only [Matrix.sum_apply] using congrFun (congrFun (S.B y).sum_eq_one i.2) j.2]
  calc
    _ =
        (inner ℂ S.ψ
          (applyOperatorToState
            (∑ b : G.AnswerB,
              heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re := by
          simp [outcomeWeight, applyOperatorToState]
    _ = (inner ℂ S.ψ
        (applyOperatorToState (heteroKron ((S.A x).effect a) 1) S.ψ)).re := by
      rw [hsum]
    _ = _ := rfl

/-- Every answer event has nonnegative Born weight. -/
theorem outcome_event_weight_nonneg :
    0 ≤ outcomeEventWeight S x y E := by
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs
    · apply outcomeWeight_nonneg
    · exact le_rfl

/-- An answer event depending only on Alice has its Alice marginal weight. -/
theorem outcome_event_weight_left_eq
    (E : G.AnswerA → Prop) [DecidablePred E] :
    outcomeEventWeight S x y (fun a _ => E a) = aliceEventWeight S x E := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a
  · simp [ha, sum_outcome_weight_right]
  · simp [ha]

/-- Inclusion of answer events implies the corresponding Born-weight inequality. -/
theorem outcome_event_weight_mono [DecidableRel F]
    (hEF : ∀ a b, E a b → F a b) :
    outcomeEventWeight S x y E ≤ outcomeEventWeight S x y F := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases hE : E a b
  · simp [*]
  · split_ifs
    · apply outcomeWeight_nonneg
    · exact le_rfl

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
  rw [show avgOver G.μ (fun questions =>
      ∑ a, ∑ b,
        if G.decide questions.1 questions.2 a b then 0
        else outcomeWeight S questions.1 questions.2 a b) =
      _ by
    apply avgOver_congr
    intro questions
    calc
      _ =
          ∑ a, ∑ b,
            (outcomeWeight S questions.1 questions.2 a b -
              if G.decide questions.1 questions.2 a b then
                outcomeWeight S questions.1 questions.2 a b else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        split <;> simp
      _ = (∑ a, ∑ b, outcomeWeight S questions.1 questions.2 a b) -
          ∑ a, ∑ b,
            if G.decide questions.1 questions.2 a b then
              outcomeWeight S questions.1 questions.2 a b else 0 := by
        simp
      _ = _ := by
        rw [outcomeWeight_sum_eq_one]]
  rw [avgOver_sub, avgOver_const_of_isProbability G.μ G.μ_prob]
  rfl

end

/-- Every strategy value is at most one.  Formalization-only support for
blueprint `def:tensor-product-value`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-57`. -/
theorem Strategy.value_le_one {G : Game} (S : Strategy G) : S.value ≤ 1 := by
  have hnn :
      0 ≤ avgOver G.μ (fun questions =>
        ∑ a, ∑ b,
          if G.decide questions.1 questions.2 a b then 0
          else outcomeWeight S questions.1 questions.2 a b) :=
    avgOver_nonneg _ _ fun questions =>
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
        split_ifs
        · exact le_rfl
        · apply outcomeWeight_nonneg
  rw [rejectionMass_eq_one_sub_value] at hnn
  linarith

end MIPStarRE.QPBT
