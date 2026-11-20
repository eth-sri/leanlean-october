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
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## From a direct strategy to an LDT strategy -/

section

variable {alpha iota : Type*} [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha iota)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
include alpha iota M hM

/-- Regard a matrix-valued projective measurement as a projective measurement
of the low individual degree test. -/
noncomputable def matrixMeasurementToLDTProjMeas :
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

@[simp] theorem matrixMeasurementToLDTProjMeas_outcome (a : alpha) :
    (matrixMeasurementToLDTProjMeas M hM).outcome a = M.effect a :=
  rfl

end

/-- Query a projective direct strategy and read a component of its answer. -/
noncomputable abbrev directCoordinateReadout {D : DirectLdParams} {X A ι : Type*}
    [Fintype A] [Fintype ι] [DecidableEq ι]
    (M : DirectLdQuestion D → MIPStarRE.Quantum.Measurement (DirectLdAnswer D) ι)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q))
    (q : X → DirectLdQuestion D) (f : X → DirectLdAnswer D → A) : IdxProjMeas X A ι :=
  fun x => (matrixMeasurementToLDTProjMeas (M (q x)) (hM (q x))).postprocess (f x)

section

variable (D : DirectLdParams) (r : Fin D.k)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (M : DirectLdQuestion D → MIPStarRE.Quantum.Measurement (DirectLdAnswer D) ι)
  (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q))

/-- Read one simultaneous coordinate of the point answers. -/
def directCoordinatePointMeasurement :
    letI := D.toLDTFieldModel
    IdxProjMeas (Point D.toLDTParameters) (Fq D.toLDTParameters) ι :=
  letI := D.toLDTFieldModel
  directCoordinateReadout M hM (directPointQuestionOf D) (fun _ => directPointAnswerReadout D r)

/-- Query the canonical axis line and rebase the answer to the given parametrization. -/
def directCoordinateAxisMeasurement :
    letI := D.toLDTFieldModel
    IdxProjMeas (AxisParallelLine D.toLDTParameters) (AxisLinePolynomial D.toLDTParameters) ι :=
  letI := D.toLDTFieldModel
  directCoordinateReadout M hM (directAxisQuestionOf D) (directAxisAnswerReadout D r)

/-- Query the canonical diagonal line and rebase the answer to the given parametrization. -/
def directCoordinateDiagonalMeasurement :
    letI := D.toLDTFieldModel
    IdxProjMeas (DiagonalLine D.toLDTParameters) (DiagonalLinePolynomial D.toLDTParameters) ι :=
  letI := D.toLDTFieldModel
  directCoordinateReadout M hM (directDiagonalQuestionOf D) (directDiagonalAnswerReadout D r)

/-- If a change of presentation relabels answers by a permutation, the
transported outcome of the readout is unchanged. -/
private theorem readout_reparam {X A : Type*} [Fintype A]
    {q : X → DirectLdQuestion D} {f : X → DirectLdAnswer D → A} {x y : X}
    (hq : q x = q y) (e : A ≃ A) (hf : ∀ a, f x a = e (f y a)) (b : A) :
    (directCoordinateReadout M hM q f x).outcome (e b) =
      (directCoordinateReadout M hM q f y).outcome b := by
  classical
  simp_all

/-- The axis-line family is invariant under affine reparametrization. -/
theorem directCoordinateAxisMeasurement_reparam :
    letI := D.toLDTFieldModel
    AxisParallelMeasurementReparamInvariant D.toLDTParameters
      (directCoordinateAxisMeasurement D r M hM) := by
  letI := D.toLDTFieldModel
  intro line t f
  exact readout_reparam D M hM (directAxisQuestionOf_rebase D line t)
    (AxisLinePolynomial.reparamAtEquiv t) (directAxisAnswerReadout_rebase D r line t) f

/-- The diagonal-line family is invariant under affine reparametrization, including zero directions. -/
theorem directCoordinateDiagonalMeasurement_reparam :
    letI := D.toLDTFieldModel
    DiagonalMeasurementReparamInvariant D.toLDTParameters
      (directCoordinateDiagonalMeasurement D r M hM) := by
  letI := D.toLDTFieldModel
  intro line t f
  exact readout_reparam D M hM (directDiagonalQuestionOf_rebase D line t)
    (DiagonalLinePolynomial.reparamAtEquiv t) (directDiagonalAnswerReadout_rebase D r line t) f

end

section

variable {G : Game} (S : Strategy G)
include G S

private theorem strategy_carrier_nonempty :
    Nonempty (S.ιA × S.ιB) := by
  by_contra h
  rw [not_nonempty_iff] at h
  letI := h
  have hzero : S.ψ = 0 := Subsingleton.elim _ _
  have hnorm := S.ψ_norm
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

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
  letI := strategy_carrier_nonempty S
  simpa [strategyQuantumState] using
    PureState.toQuantumState_isNormalized (strategyPureState S)

end

/-- The complex Born amplitude of a vector and two local effects. -/
private noncomputable def vectorBornAmplitude
    {iotaA iotaB : Type*}
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (psi : EuclideanSpace ℂ (iotaA × iotaB))
    (A : Op iotaA) (B : Op iotaB) : ℂ :=
  inner ℂ psi (applyOperatorToState (heteroKron A B) psi)

section

variable {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (ψ : EuclideanSpace ℂ (I × J)) (φ : EuclideanSpace ℂ ((I × R) × (J × R)))
    (hφ : ∀ i j r s, φ ((i, r), (j, s)) =
      if r = s then ψ (i, j) * (Real.sqrt (Fintype.card R : ℝ) : ℂ)⁻¹ else 0)
    (A : Op (I × R)) (B : R → Op J)
include I J R ψ φ hφ A B

/-- Opposite a block-diagonal operator on a correlated residue state, only the
matching diagonal blocks contribute to the Born amplitude. -/
private theorem correlatedBlockAmplitude :
    vectorBornAmplitude φ A (Matrix.blockDiagonal B) =
      (Fintype.card R : ℂ)⁻¹ * ∑ r, vectorBornAmplitude ψ
        (A.submatrix (fun i => (i, r)) (fun i => (i, r))) (B r) := by
  classical
  unfold vectorBornAmplitude applyOperatorToState heteroKron Matrix.kronecker
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [hφ, Matrix.blockDiagonal_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Finset.mul_sum, apply_ite, ite_mul, mul_ite, mul_assoc, mul_comm]
  rw [Finset.sum_comm]
  iterate 5 refine Fintype.sum_congr _ _ fun _ => ?_
  rw [← inv_sqrt_natCast_mul_self (Fintype.card R)]
  ring

/-- The real Born weight is the uniform sum of the matching block weights. -/
theorem correlatedState_blockDiagonal_right :
    stateQForm φ (heteroKron A (Matrix.blockDiagonal B)) =
      (Fintype.card R : ℝ)⁻¹ * ∑ r, stateQForm ψ
        (heteroKron (A.submatrix (fun i => (i, r)) (fun i => (i, r))) (B r)) := by
  change (vectorBornAmplitude _ _ _).re = _ * ∑ _, (vectorBornAmplitude _ _ _).re
  simp_all [correlatedBlockAmplitude ψ φ hφ, Complex.mul_re, Complex.inv_re, Complex.inv_im]

end

private theorem seedFiberBlockBornWeight {G : Game} (S : Strategy G) (L : LdParams)
    (A : SeedResidue L → Op S.ιA) (B : SeedResidue L → Op S.ιB) :
    stateQForm (seedFiberLiftedState S L)
        (heteroKron (Matrix.blockDiagonal A) (Matrix.blockDiagonal B)) =
      (Fintype.card (SeedResidue L) : ℝ)⁻¹ *
        ∑ residue, stateQForm S.ψ (heteroKron (A residue) (B residue)) := by
  letI := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  rw [correlatedState_blockDiagonal_right _ _ (seedFiberLiftedState_apply S L)]
  congr 1
  apply Fintype.sum_congr
  intro r
  congr 2
  ext i j
  simp [Matrix.blockDiagonal_apply]

/-- The Born weight of the direct strategy obtained by dilating a seed-indexed
strategy with a correlated residue register is the uniform average of the
original seed-dependent Born weights over that residue. -/
theorem ldStrategyToDirect_bornWeight
    (L : LdParams) (S : Strategy (ldGame L))
    (x y : DirectLdQuestion L.toDirectLdParams)
    (a b : DirectLdAnswer L.toDirectLdParams) :
    outcomeWeight (ldStrategyToDirect L S) x y a b =
      (Fintype.card (SeedResidue L) : ℝ)⁻¹ *
        ∑ residue,
          outcomeWeight S
            (seededLdQuestion L x residue)
            (seededLdQuestion L y residue)
            ((ldDirectAnswerEquiv L).symm a)
            ((ldDirectAnswerEquiv L).symm b) := by
  change stateQForm (seedFiberLiftedState S L) (heteroKron
      (Matrix.blockDiagonal fun residue =>
        (S.A (seededLdQuestion L x residue)).effect
          ((ldDirectAnswerEquiv L).symm a))
      (Matrix.blockDiagonal fun residue =>
        (S.B (seededLdQuestion L y residue)).effect
          ((ldDirectAnswerEquiv L).symm b))) = _
  exact seedFiberBlockBornWeight S L _ _

/-- Read coordinate `r` of a projective direct-game strategy as a two-space
projective strategy for the low individual degree test. -/
noncomputable def directCoordinateProjStrat
    (D : DirectLdParams) (S : Strategy (directLdGame D))
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
