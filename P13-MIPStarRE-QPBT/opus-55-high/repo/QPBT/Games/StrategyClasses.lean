module
public import QPBT.Games.Defs
public import QPBT.Games.Consistency
public import QPBT.State
public import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull
public import MIPStarRE.LDT.Preliminaries.Completion
public import MIPStarRE.LDT.Test.StrategyBiProj.DirectSum

/-! # Strategy classes and symmetric games

This module defines projective, commuting, consistent, PCC, and SPCC strategy
predicates from blueprint `def:projective-strategy-general`,
`def:symmetric-game`, `def:comm-strategy`, `def:consistent-measurement`,
`def:consistent-strategy`, and `def:spcc`, with source definitions in
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:68-180`.
-/
@[expose] public section
namespace MIPStarRE.QPBT

universe u

open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.LDT MIPStarRE.Quantum

/-- Projectivity from blueprint
`def:projective-strategy-general`, paper `06_nonlocal_games_and_mipstar.tex:68-72`. -/
def Strategy.IsProjective {G : Game} (S : Strategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.A x)) ∧
    ∀ y, MIPStarRE.QPBT.Measurement.IsProjective (S.B y)

/-- Symmetric games from blueprint
`def:symmetric-game`, paper `06_nonlocal_games_and_mipstar.tex:74-92`.
The question and answer alphabets are each represented by a single shared type,
matching the source notation. -/
structure SymmetricGame where
  Question : Type
  Answer : Type
  [questionFintype : Fintype Question]
  [answerFintype : Fintype Answer]
  [questionDecidableEq : DecidableEq Question]
  [answerDecidableEq : DecidableEq Answer]
  μ : Distribution (Question × Question)
  μ_prob : μ.IsProbability
  μ_symm : ∀ x y, μ.weight (x, y) = μ.weight (y, x)
  decide : Question → Question → Answer → Answer → Bool
  decide_symm : ∀ x y a b, decide x y a b = decide y x b a

attribute [instance] SymmetricGame.questionFintype SymmetricGame.answerFintype
  SymmetricGame.questionDecidableEq SymmetricGame.answerDecidableEq

/-- Regard a symmetric game as a game with equal question and answer types;
blueprint
`def:symmetric-game`, paper `06_nonlocal_games_and_mipstar.tex:74-92`. -/
def SymmetricGame.toGame (G : SymmetricGame) : Game where
  QuestionA := G.Question
  QuestionB := G.Question
  AnswerA := G.Answer
  AnswerB := G.Answer
  μ := G.μ
  μ_prob := G.μ_prob
  decide := G.decide

/-- Symmetric strategies from blueprint
`def:symmetric-game`, paper `06_nonlocal_games_and_mipstar.tex:74-92`.
The two local spaces and measurement families are identified, as in the source
definition. -/
structure SymmetricStrategy (G : SymmetricGame) where
  ι : Type
  [ιFintype : Fintype ι]
  [ιDecidableEq : DecidableEq ι]
  ψ : EuclideanSpace ℂ (ι × ι)
  ψ_norm : ‖ψ‖ = 1
  ψ_swap : reindexState (Equiv.prodComm ι ι) ψ = ψ
  M : G.Question → MIPStarRE.Quantum.Measurement G.Answer ι

attribute [instance] SymmetricStrategy.ιFintype SymmetricStrategy.ιDecidableEq

/-- Regard a symmetric strategy as a strategy using the same local space and
measurement family for both players; blueprint
`def:symmetric-game`, paper `06_nonlocal_games_and_mipstar.tex:74-92`. -/
def SymmetricStrategy.toStrategy {G : SymmetricGame} (S : SymmetricStrategy G) :
    Strategy G.toGame where
  ιA := S.ι
  ιB := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A := S.M
  B := S.M

/-- Common-space commutation from blueprint
`def:comm-strategy`, paper `06_nonlocal_games_and_mipstar.tex:132-142`. -/
def IsCommutingOn {X Y α β ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (μ : Distribution (X × Y))
    (A : X → MIPStarRE.Quantum.Measurement α ι)
    (B : Y → MIPStarRE.Quantum.Measurement β ι) : Prop :=
  ∀ x y, 0 < μ.weight (x, y) → ∀ a b, Commute ((A x).effect a) ((B y).effect b)

/-- Measurement consistency from blueprint
`def:consistent-measurement`, paper `06_nonlocal_games_and_mipstar.tex:144-160`. -/
def Measurement.IsConsistentOn {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  ∀ a, (heteroKron (M.effect a) 1).mulVec ψ =
    (heteroKron 1 (M.effect a)).mulVec ψ

/-- Symmetric strategy consistency from blueprint
`def:consistent-strategy`, paper `06_nonlocal_games_and_mipstar.tex:162-174`. -/
def SymmetricStrategy.IsConsistent {G : SymmetricGame}
    (S : SymmetricStrategy G) : Prop :=
  ∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (S.M x) S.ψ

/-- The SPCC predicate blueprint `def:spcc`,
paper `06_nonlocal_games_and_mipstar.tex:176-180`. -/
def SymmetricStrategy.IsSPCC {G : SymmetricGame}
  (S : SymmetricStrategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.M x)) ∧ S.IsConsistent ∧
    IsCommutingOn G.μ S.M S.M

noncomputable section

open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.Preliminaries

/-- The real quadratic form of an operator evaluated on a finite vector. This
is the Born expression averaged by blueprint
`def:tensor-product-value`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-48`. -/
def vectorQForm {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : EuclideanSpace ℂ I) (A : Op I) : ℝ :=
  (inner ℂ ψ (Matrix.toEuclideanLin A ψ)).re

/-- Embed a bipartite state into one distinguished coordinate of each local
ancilla space, extending it by zero elsewhere. This is the zero padding used by
the dilations of blueprint
`def:projective-strategy-general`, and of blueprint
`lem:projective-strategy-setup`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:155-172`. -/
def padState
    {I J κA κB : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB]
    (aA : κA) (bB : κB) (ψ : EuclideanSpace ℂ (I × J)) :
    EuclideanSpace ℂ ((I × κA) × (J × κB)) :=
  (EuclideanSpace.equiv ((I × κA) × (J × κB)) ℂ).symm
    (fun p => if p.1.2 = aA then
      if p.2.2 = bB then ψ.ofLp (p.1.1, p.2.1) else 0 else 0)

/-- Padding a state at the two distinguished ancilla coordinates preserves its
norm. -/
theorem padState_norm
    {I J κA κB : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB]
    (aA : κA) (bB : κB) (ψ : EuclideanSpace ℂ (I × J)) :
    ‖padState aA bB ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [padState, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single aA]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single bB]
    · simp
    · simp_all
    simp
  · simp_all
  simp

/-- The quadratic form of a padded state depends only on the compression of
each local operator at the distinguished ancilla coordinate. -/
theorem stateQForm_padState
    {I J κA κB : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB]
    (aA : κA) (bB : κB) (ψ : EuclideanSpace ℂ (I × J))
    (A : Op I) (B : Op J) (A' : Op (I × κA)) (B' : Op (J × κB))
    (hA : ∀ i j, A' (i, aA) (j, aA) = A i j)
    (hB : ∀ i j, B' (i, bB) (j, bB) = B i j) :
    vectorQForm (padState aA bB ψ) (heteroKron A' B') =
      vectorQForm ψ (heteroKron A B) := by
  apply congrArg Complex.re
  change (∑ p : (I × κA) × (J × κB),
      (∑ q : (I × κA) × (J × κB),
        heteroKron A' B' p q * (padState aA bB ψ).ofLp q) *
        star (padState aA bB ψ).ofLp p) =
    (∑ p : I × J,
      (∑ q : I × J, heteroKron A B p q * ψ.ofLp q) * star ψ.ofLp p)
  suffices hExpanded :
      (∑ i : I, ∑ a : κA, ∑ j : J, ∑ b : κB,
        (∑ k : I, ∑ l : J,
          A' (i, a) (k, aA) * B' (j, b) (l, bB) * ψ.ofLp (k, l)) *
            star (if a = aA then if b = bB then ψ.ofLp (i, j) else 0 else 0)) =
        ∑ i : I, ∑ j : J,
          (∑ k : I, ∑ l : J, A i k * B j l * ψ.ofLp (k, l)) *
            star (ψ.ofLp (i, j)) by
    simpa [padState, heteroKron, Matrix.kronecker,
      Fintype.sum_prod_type] using hExpanded
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single aA]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single bB]
    · simp_all
    · simp_all
    simp
  · simp_all
  simp

variable {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]

/-- Choose the one-measurement Naimark dilation data for a POVM. -/
def oneMeasData
    (M : MIPStarRE.Quantum.Measurement α I) : OneMeasNaimarkData α I :=
  Classical.choose (oneMeasNaimark M.toSubmeasurement)

/-- The source submeasurement of the chosen Naimark data is the original POVM. -/
theorem oneMeasData_source_effect
    (M : MIPStarRE.Quantum.Measurement α I) :
    (oneMeasData M).source.effect = M.effect :=
  congrArg MIPStarRE.Quantum.Submeasurement.effect
    (Classical.choose_spec (oneMeasNaimark M.toSubmeasurement))

/-- Complete the Naimark projectors at one outcome to obtain a projective POVM. -/
def dilatedMeasurement
    (a₀ : α) (M : MIPStarRE.Quantum.Measurement α I) :
    MIPStarRE.Quantum.Measurement α (I × Option α) :=
  let P := completeAtOutcomeProj (oneMeasData M).toProjSubMeas a₀
  MIPStarRE.Quantum.Measurement.ofSumEqOne P.outcome P.outcome_pos <| by
    rw [P.sum_eq_total, P.total_eq_one]

/-- Every effect of the completed Naimark measurement is a projection. -/
theorem dilatedMeasurement_isProjective
    (a₀ : α) (M : MIPStarRE.Quantum.Measurement α I) :
    MIPStarRE.QPBT.Measurement.IsProjective (dilatedMeasurement a₀ M) := by
  intro a
  let P := completeAtOutcomeProj (oneMeasData M).toProjSubMeas a₀
  exact
    { isIdempotentElem := P.proj a
      isSelfAdjoint :=
        (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a)).isHermitian.eq }

/-- Compressing a completed Naimark effect to the distinguished ancilla
coordinate recovers the original POVM effect. -/
theorem dilatedMeasurement_compression
    (a₀ a : α) (M : MIPStarRE.Quantum.Measurement α I) (i j : I) :
    (dilatedMeasurement a₀ M).effect a (i, none) (j, none) = M.effect a i j := by
  let D := oneMeasData M
  let P := D.toProjSubMeas
  have hcompress (b : α) : P.outcome b (i, none) (j, none) = M.effect b i j := by
    change D.liftedEffect (some b) (i, none) (j, none) = M.effect b i j
    rw [D.compression_none_none]
    exact congrArg (fun X : Op I => X i j)
      (congrFun (oneMeasData_source_effect M) b)
  have htotal : P.total (i, none) (j, none) = (1 : Op I) i j := by
    rw [← P.sum_eq_total]
    simp_rw [Matrix.sum_apply, hcompress]
    simpa [Matrix.sum_apply] using congrArg (fun X : Op I => X i j) M.sum_eq_one
  change ((completeAtOutcomeProj P a₀).toMeasurement).outcome a
      (i, none) (j, none) = M.effect a i j
  rw [completeAtOutcomeProj_toMeasurement]
  simp only [completeAtOutcome]
  by_cases ha : a = a₀
  · subst a
    simp_all [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
  simp_all

variable {G : Game} (S : Strategy G) {κA κB : Type} [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]

/-- Replace both local measurement families of a strategy by families on the
enlarged local registers and pad the state at the distinguished ancilla
coordinates. This is the dilation step shared by
blueprint `def:projective-strategy-general`, and
blueprint
`lem:projective-strategy-setup`. -/
@[reducible] def paddedStrategy (aA : κA) (bB : κB)
    (A' : G.QuestionA → MIPStarRE.Quantum.Measurement G.AnswerA (S.ιA × κA))
    (B' : G.QuestionB → MIPStarRE.Quantum.Measurement G.AnswerB (S.ιB × κB)) :
    Strategy G where
  ιA := S.ιA × κA
  ιB := S.ιB × κB
  ψ := padState aA bB S.ψ
  ψ_norm := (padState_norm aA bB S.ψ).trans S.ψ_norm
  A := A'
  B := B'

/-- The padded strategy is projective as soon as both enlarged families are. -/
theorem paddedStrategy_isProjective (aA : κA) (bB : κB)
    (A' : G.QuestionA → MIPStarRE.Quantum.Measurement G.AnswerA (S.ιA × κA))
    (B' : G.QuestionB → MIPStarRE.Quantum.Measurement G.AnswerB (S.ιB × κB))
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A' x))
    (hB : ∀ y, MIPStarRE.QPBT.Measurement.IsProjective (B' y)) :
    (paddedStrategy S aA bB A' B').IsProjective :=
  ⟨fun x => hA x, fun y => hB y⟩

/-- Local dilation and padding preserve every game correlation, hence the
strategy value, as soon as each enlarged family compresses to the original one
at the distinguished ancilla coordinate. -/
theorem paddedStrategy_value (aA : κA) (bB : κB)
    (A' : G.QuestionA → MIPStarRE.Quantum.Measurement G.AnswerA (S.ιA × κA))
    (B' : G.QuestionB → MIPStarRE.Quantum.Measurement G.AnswerB (S.ιB × κB))
    (hA : ∀ x a i j, (A' x).effect a (i, aA) (j, aA) = (S.A x).effect a i j)
    (hB : ∀ y b i j, (B' y).effect b (i, bB) (j, bB) = (S.B y).effect b i j) :
    (paddedStrategy S aA bB A' B').value = S.value := by
  apply avgOver_congr
  intro xy
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hw : G.decide xy.1 xy.2 a b
  · simp only [hw, if_true]
    exact stateQForm_padState aA bB S.ψ ((S.A xy.1).effect a)
      ((S.B xy.2).effect b) ((A' xy.1).effect a) ((B' xy.2).effect b)
      (hA xy.1 a) (hB xy.2 b)
  simp_all

/-- Transport a POVM along an equivalence of its finite coordinate type. -/
noncomputable def reindexMeasurement
    {α I J : Type*} [Fintype α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (M : MIPStarRE.Quantum.Measurement α J) :
    MIPStarRE.Quantum.Measurement α I :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => reindexOp e (M.effect a))
    (fun a => MIPStarRE.Quantum.reindex_nonneg e.symm (M.pos a))
    (by
      change ∑ a : α, (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) = 1
      rw [← map_sum, M.sum_eq_one, map_one])

/-- Reindexing a projective POVM preserves projectivity. -/
theorem reindexMeasurement_isProjective
    {α I J : Type*} [Fintype α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (M : MIPStarRE.Quantum.Measurement α J)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (reindexMeasurement e M) := by
  intro a
  change IsProj (reindexOp e (M.effect a))
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) *
        (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) =
      (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a)
    rw [← map_mul, (hM a).isIdempotentElem.eq]
  · exact (Matrix.IsHermitian.ext fun i j => by
      simp [reindexOp, Matrix.reindex_apply,
        (hM a).isSelfAdjoint.isHermitian.apply]).isSelfAdjoint

namespace SymmetrizationObstruction

end SymmetrizationObstruction

end

end MIPStarRE.QPBT
