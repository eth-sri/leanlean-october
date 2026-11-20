module

public import QPBT.Combining.DirectLowDegree.Transport.Questions
public import QPBT.Combining.DirectLowDegree.Transport.SeedFiber

/-!
# Strategy transport for the directly indexed low-degree game

This module reads one coordinate of a projective directly indexed strategy as
a two-space low individual degree test strategy.  The question and answer
transport of `Transport.Questions` supplies the canonical direct question of
every LDT line, with the reversed coordinate order and the leading index of
the decoded diagonal direction, together with answer readouts that are
covariant under line rebasing; this establishes all four covariance
conditions of `ProjStrat`.  The module also records exact Born-weight
formulas for both directions of strategy transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `references/ldt-paper/test_definition.tex:49-151`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## From a direct strategy to an LDT strategy -/

section

variable (D : DirectLdParams) {G : Game} {alpha : Type*} (S : Strategy G) (r : Fin D.k)
  {iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
  (M : MIPStarRE.Quantum.Measurement alpha iota)

/-- Regard a matrix-valued projective measurement as a projective measurement
of the low individual degree test. -/
noncomputable def matrixMeasurementToLDTProjMeas
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.LDT.ProjMeas alpha iota where
  toMeasurement := {
    toSubMeas := {
      outcome := M.effect
      total := 1
      outcome_pos := M.pos
      sum_eq_total := M.sum_eq_one
      total_le_one := le_rfl
    }
    total_eq_one := rfl
  }
  proj a := (hM a).isIdempotentElem.eq

@[simp] theorem matrixMeasurementToLDTProjMeas_outcome
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (a : alpha) :
    (matrixMeasurementToLDTProjMeas M hM).outcome a = M.effect a :=
  rfl

/-- Point measurements obtained by querying the direct strategy and reading
one simultaneous coordinate. -/
noncomputable def directCoordinatePointMeasurement
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    IdxProjMeas (Point D.toLDTParameters) (Fq D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro u
  exact ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (M (directPointQuestionOf u))
      (hM (directPointQuestionOf u)))
    (directPointAnswerReadout r)

/-- Axis-line measurements obtained by querying the canonical direct line and
rebasing one coordinate polynomial to the LDT line parametrization. -/
noncomputable def directCoordinateAxisMeasurement
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    IdxProjMeas (AxisParallelLine D.toLDTParameters)
      (AxisLinePolynomial D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro line
  exact ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (M (directAxisQuestionOf D line))
      (hM (directAxisQuestionOf D line)))
    (directAxisAnswerReadout D r line)

/-- Diagonal-line measurements obtained by querying the canonical direct line
and rebasing one coordinate polynomial to the LDT line parametrization. -/
noncomputable def directCoordinateDiagonalMeasurement
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    IdxProjMeas (DiagonalLine D.toLDTParameters)
      (DiagonalLinePolynomial D.toLDTParameters) iota := by
  letI := D.toLDTFieldModel
  intro line
  exact ProjMeas.postprocess
    (matrixMeasurementToLDTProjMeas (M (directDiagonalQuestionOf line))
      (hM (directDiagonalQuestionOf line)))
    (directDiagonalAnswerReadout D r line)

/-- The coordinate axis-line family is independent of the chosen affine
parametrization of an LDT line. -/
theorem directCoordinateAxisMeasurement_reparam
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    AxisParallelMeasurementReparamInvariant D.toLDTParameters
      (directCoordinateAxisMeasurement D r M hM) := by
  letI := D.toLDTFieldModel
  classical
  intro line t f
  simp [directCoordinateAxisMeasurement]
  rw [directAxisQuestionOf_rebase]
  have hfiber :
      Finset.univ.filter (fun answer =>
        directAxisAnswerReadout D r (line.rebaseAt t) answer =
          AxisLinePolynomial.reparamAt f t) =
        Finset.univ.filter (fun answer =>
          directAxisAnswerReadout D r line answer = f) := by
    ext answer
    simp
    rw [directAxisAnswerReadout_rebase]
    exact (AxisLinePolynomial.reparamAtEquiv t).injective.eq_iff
  rw [hfiber]

/-- The coordinate diagonal-line family is independent of the chosen affine
parametrization, including the zero-direction convention. -/
theorem directCoordinateDiagonalMeasurement_reparam
    (M : DirectLdQuestion D →
      MIPStarRE.Quantum.Measurement (DirectLdAnswer D) iota)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q)) :
    letI := D.toLDTFieldModel
    DiagonalMeasurementReparamInvariant D.toLDTParameters
      (directCoordinateDiagonalMeasurement D r M hM) := by
  letI := D.toLDTFieldModel
  classical
  intro line t f
  simp [directCoordinateDiagonalMeasurement]
  rw [directDiagonalQuestionOf_rebase]
  have hfiber :
      Finset.univ.filter (fun answer =>
        directDiagonalAnswerReadout D r (line.rebaseAt t) answer =
          DiagonalLinePolynomial.reparamAt f t) =
        Finset.univ.filter (fun answer =>
          directDiagonalAnswerReadout D r line answer = f) := by
    ext answer
    simp
    rw [directDiagonalAnswerReadout_rebase]
    exact (DiagonalLinePolynomial.reparamAtEquiv t).injective.eq_iff
  rw [hfiber]

private theorem strategy_carrier_nonempty :
    Nonempty (S.ιA × S.ιB) := by
  by_contra h
  rw [not_nonempty_iff] at h
  letI := h
  have hzero : S.ψ = 0 := Subsingleton.elim _ _
  have hnorm := S.ψ_norm
  simp_all

/-- The pure LDT state represented by a game's unit strategy vector. -/
noncomputable def strategyPureState
    [Nonempty (S.ιA × S.ιB)] : PureState (S.ιA × S.ιB) where
  vector := S.ψ
  unit := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, S.ψ_norm]
    norm_num

/-- The density-matrix state represented by a game's unit strategy vector. -/
noncomputable def strategyQuantumState :
    QuantumState (S.ιA × S.ιB) := by
  letI : Nonempty (S.ιA × S.ιB) := by
    exact strategy_carrier_nonempty S
  exact PureState.toQuantumState (strategyPureState S)

/-- The density-matrix state associated with a game strategy is normalized. -/
theorem strategyQuantumState_isNormalized :
    (strategyQuantumState S).IsNormalized := by
  solve_by_elim [strategy_carrier_nonempty, PureState.toQuantumState_isNormalized]

end

section

variable {alpha beta iotaA iotaB : Type*} [Fintype iotaA] [DecidableEq iotaA] [Fintype iotaB]
  [DecidableEq iotaB] (psi : EuclideanSpace ℂ (iotaA × iotaB)) (A A₁ A₂ : Op iotaA)
  (B₁ B B₂ : Op iotaB)

/-- The complex Born amplitude of a vector and two local effects. -/
private noncomputable def vectorBornAmplitude : ℂ :=
  inner ℂ psi (applyOperatorToState (heteroKron A B) psi)

/-- The real Born quadratic form of a vector and two local effects. -/
private noncomputable def vectorBornWeight : ℝ :=
  (vectorBornAmplitude psi A B).re

private theorem vectorBornAmplitude_add_left :
    vectorBornAmplitude psi (A₁ + A₂) B =
      vectorBornAmplitude psi A₁ B + vectorBornAmplitude psi A₂ B := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.add_kronecker]
  simp

private theorem vectorBornAmplitude_add_right :
    vectorBornAmplitude psi A (B₁ + B₂) =
      vectorBornAmplitude psi A B₁ + vectorBornAmplitude psi A B₂ := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  rw [Matrix.kronecker_add]
  simp

private theorem vectorBornAmplitude_zero_left :
    vectorBornAmplitude psi 0 B = 0 := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  simp

private theorem vectorBornAmplitude_zero_right :
    vectorBornAmplitude psi A 0 = 0 := by
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  simp

private theorem vectorBornWeight_add_left :
    vectorBornWeight psi (A₁ + A₂) B =
      vectorBornWeight psi A₁ B + vectorBornWeight psi A₂ B := by
  unfold vectorBornWeight
  simp [vectorBornAmplitude_add_left]

private theorem vectorBornWeight_add_right :
    vectorBornWeight psi A (B₁ + B₂) =
      vectorBornWeight psi A B₁ + vectorBornWeight psi A B₂ := by
  unfold vectorBornWeight
  simp [vectorBornAmplitude_add_right]

private theorem vectorBornWeight_finset_sum_left
    (s : Finset alpha) (A : alpha → Op iotaA) (B : Op iotaB) :
    vectorBornWeight psi (∑ a ∈ s, A a) B =
      ∑ a ∈ s, vectorBornWeight psi (A a) B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [vectorBornWeight, vectorBornAmplitude_zero_left]
  | @insert a s ha ih =>
      simp [Finset.sum_insert ha, vectorBornWeight_add_left, ih]

private theorem vectorBornWeight_finset_sum_right (s : Finset beta) (B : beta → Op iotaB) :
    vectorBornWeight psi A (∑ b ∈ s, B b) =
      ∑ b ∈ s, vectorBornWeight psi A (B b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [vectorBornWeight, vectorBornAmplitude_zero_right]
  | @insert b s hb ih =>
      simp [Finset.sum_insert hb, vectorBornWeight_add_right, ih]

end

variable (D : DirectLdParams) {G : Game} (S : Strategy G) (L : LdParams)
  (A : Fin (L.q / L.m) → Op S.ιA) (B : Fin (L.q / L.m) → Op S.ιB)

/-- Expectations in the density state associated with a strategy agree with
the strategy's vector Born quadratic form. -/
private theorem strategyQuantumState_ev_eq_vectorBornWeight (A : Op S.ιA) (B : Op S.ιB) :
    ev (strategyQuantumState S) (opTensor A B) =
      vectorBornWeight S.ψ A B := by
  letI := strategy_carrier_nonempty S
  rw [show strategyQuantumState S =
      PureState.toQuantumState (strategyPureState S) by
        simp [strategyQuantumState],
    PureState.ev_eq_re_inner]
  change (star S.ψ ⬝ᵥ
      (Matrix.kronecker A B *ᵥ S.ψ)).re =
    ((Matrix.kronecker A B *ᵥ S.ψ) ⬝ᵥ star S.ψ).re
  rw [dotProduct_comm]

/-- Postprocessing both local measurements gives the exact double sum of the
original Born weights over the two answer fibers. -/
theorem directPostprocessBornWeight (S : Strategy (directLdGame D))
    (hS : S.IsProjective)
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (x y : DirectLdQuestion D)
    (readA : DirectLdAnswer D → alpha)
    (readB : DirectLdAnswer D → beta)
    (a : alpha) (b : beta) :
    ev (strategyQuantumState S)
        (opTensor
          ((ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).outcome a)
          ((ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).outcome b)) =
      ∑ directA ∈ Finset.univ.filter (fun answer => readA answer = a),
        ∑ directB ∈ Finset.univ.filter (fun answer => readB answer = b),
          outcomeWeight S x y directA directB := by
  rw [strategyQuantumState_ev_eq_vectorBornWeight]
  simp
  rw [vectorBornWeight_finset_sum_left]
  congr 1 with directA
  rw [vectorBornWeight_finset_sum_right]
  rfl

/-- Correlated residue registers turn two block-diagonal effects into the
uniform average of their matching source-block Born weights. -/
private theorem seedFiberBlockBornAmplitude :
    vectorBornAmplitude (seedFiberLiftedState S L)
        (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      (Fintype.card (Fin (L.q / L.m)) : ℂ)⁻¹ *
        ∑ residue, vectorBornAmplitude S.ψ (A residue) (B residue) := by
  classical
  letI :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    dotProduct, Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [seedFiberLiftedState_apply, Matrix.blockDiagonal_apply,
    mul_assoc, mul_comm]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_comm, ← mul_assoc]
  congr 1
  apply inv_sqrt_natCast_mul_self

/-- Correlated residue registers give the uniform average of the source-block
Born weights. -/
private theorem seedFiberBlockBornWeight :
    vectorBornWeight (seedFiberLiftedState S L)
        (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
        ∑ residue, vectorBornWeight S.ψ (A residue) (B residue) := by
  unfold vectorBornWeight
  rw [seedFiberBlockBornAmplitude]
  simp

/-- The Born weight of the direct strategy obtained by dilating a seed-indexed
strategy with a correlated residue register is the uniform average of the
original seed-dependent Born weights over that residue. -/
theorem ldStrategyToDirect_bornWeight (S : Strategy (ldGame L))
    (x y : DirectLdQuestion L.toDirectLdParams)
    (a b : DirectLdAnswer L.toDirectLdParams) :
    outcomeWeight (ldStrategyToDirect S) x y a b =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
        ∑ residue,
          outcomeWeight S
            (seededLdQuestion L x residue)
            (seededLdQuestion L y residue)
            ((ldDirectAnswerEquiv L).symm a)
            ((ldDirectAnswerEquiv L).symm b) := by
  change vectorBornWeight (seedFiberLiftedState S L)
      _
      (Matrix.blockDiagonal fun residue =>
        (S.B (seededLdQuestion L y residue)).effect
          ((ldDirectAnswerEquiv L).symm b)) = _
  apply seedFiberBlockBornWeight

variable {D} in
/-- Read coordinate `r` of a projective direct-game strategy as a two-space
projective strategy for the low individual degree test. -/
noncomputable def directCoordinateProjStrat (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ProjStrat D.toLDTParameters S.ιA S.ιB := by
  letI := D.toLDTFieldModel
  exact {
    state := strategyQuantumState S
    isNormalized := strategyQuantumState_isNormalized S
    pointMeasurementA := directCoordinatePointMeasurement D r S.A hS.1
    axisParallelMeasurementA := directCoordinateAxisMeasurement D r S.A hS.1
    axisParallelReparamInvariantA :=
      directCoordinateAxisMeasurement_reparam D r S.A hS.1
    diagonalMeasurementA := directCoordinateDiagonalMeasurement D r S.A hS.1
    diagonalReparamInvariantA :=
      directCoordinateDiagonalMeasurement_reparam D r S.A hS.1
    pointMeasurementB := directCoordinatePointMeasurement D r S.B hS.2
    axisParallelMeasurementB := directCoordinateAxisMeasurement D r S.B hS.2
    axisParallelReparamInvariantB :=
      directCoordinateAxisMeasurement_reparam D r S.B hS.2
    diagonalMeasurementB := directCoordinateDiagonalMeasurement D r S.B hS.2
    diagonalReparamInvariantB :=
      directCoordinateDiagonalMeasurement_reparam D r S.B hS.2
  }

end

end MIPStarRE.QPBT
