module

public import QPBT.Combining.DirectLowDegree.Transport.Correspondence
public import QPBT.State
public import MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal

/-!
# Seed-fiber dilation for the directly indexed low-degree game

This module dilates a seed-indexed low-degree strategy by a maximally
correlated residue register.  Block-diagonal projective measurements retain
arbitrary dependence on the seed within each `chiIndex` fiber.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## Projective block measurements -/

section

variable {alpha beta iota : Type*}
    [Fintype alpha] [Fintype beta] [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota)
include alpha beta iota e M

/-- Relabel a matrix measurement along an equivalence of outcome alphabets. -/
noncomputable def matrixMeasurementTransport :
    MIPStarRE.Quantum.Measurement beta iota :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun b => M.effect (e.symm b))
    (fun b => M.pos (e.symm b))
    (Trans.trans (Equiv.sum_comp e.symm M.effect) M.sum_eq_one)

/-- Relabeling a projective matrix measurement preserves projectivity. -/
theorem matrixMeasurementTransport_isProjective
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (matrixMeasurementTransport e M) :=
  fun b => hM (e.symm b)

end

theorem blockDiagonal_finset_sum {α I R : Type*} [DecidableEq R]
    (s : Finset α) (M : α → R → Op I) :
    Matrix.blockDiagonal (fun r => ∑ a ∈ s, M a r) = ∑ a ∈ s, Matrix.blockDiagonal (M a) := by
  rw [show (fun r => ∑ a ∈ s, M a r) = ∑ a ∈ s, M a from funext fun r => by simp]
  exact map_sum (Matrix.blockDiagonalAddMonoidHom I I R ℂ) M s

section

variable {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → MIPStarRE.Quantum.Measurement alpha iota)
include alpha iota block M

/-- Assemble a family of matrix measurements as diagonal blocks indexed by a
finite classical register. -/
noncomputable def blockDiagonalMeasurement :
    MIPStarRE.Quantum.Measurement alpha (iota × block) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => Matrix.blockDiagonal fun r => (M r).effect a)
    (fun a => Matrix.blockDiagonal_nonneg
      (fun r => (M r).effect a) (fun r => (M r).pos a))
    (by
      rw [← blockDiagonal_finset_sum]
      simp only [fun r => (M r).sum_eq_one]
      exact Matrix.blockDiagonal_one)

@[simp] theorem blockDiagonalMeasurement_effect
    (a : alpha) :
    (blockDiagonalMeasurement M).effect a =
      Matrix.blockDiagonal (fun r => (M r).effect a) :=
  rfl

end

/-- A block-diagonal family of projective measurements is projective. -/
theorem blockDiagonalMeasurement_isProjective
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → MIPStarRE.Quantum.Measurement alpha iota)
    (hM : ∀ r, MIPStarRE.QPBT.Measurement.IsProjective (M r)) :
    MIPStarRE.QPBT.Measurement.IsProjective (blockDiagonalMeasurement M) := by
  intro a
  constructor
  · change Matrix.blockDiagonal (fun r => (M r).effect a) *
        Matrix.blockDiagonal (fun r => (M r).effect a) =
      Matrix.blockDiagonal (fun r => (M r).effect a)
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext r
    exact (hM r a).isIdempotentElem.eq
  · change (Matrix.blockDiagonal (fun r => (M r).effect a))ᴴ =
      Matrix.blockDiagonal (fun r => (M r).effect a)
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext r
    exact (hM r a).isSelfAdjoint.star_eq

/-! ## The correlated residue state -/

/-- The normalized maximally correlated state on the common seed-fiber
residue. -/
noncomputable def seedResidueAncilla (L : LdParams) :
    EuclideanSpace ℂ
      (SeedResidue L × SeedResidue L) := by
  letI := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact eprState (SeedResidue L)

/-- The seed-residue ancilla has unit norm. -/
theorem seedResidueAncilla_norm (L : LdParams) :
    ‖seedResidueAncilla L‖ = 1 := by
  letI := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact eprState_norm (SeedResidue L)

section

variable {G : Game} (S : Strategy G) (L : LdParams)
include G S L

/-- Tensor the original strategy state with the maximally correlated residue
state and shuffle the factors back into the two local carriers. -/
noncomputable def seedFiberLiftedState :
    EuclideanSpace ℂ
      ((S.ιA × SeedResidue L) × (S.ιB × SeedResidue L)) :=
  reindexState prodShuffle (vecTensor S.ψ (seedResidueAncilla L))

/-- The correlated seed-fiber lift preserves normalization of the strategy
state. -/
theorem seedFiberLiftedState_norm :
    ‖seedFiberLiftedState S L‖ = 1 := by
  rw [seedFiberLiftedState, reindexState_norm_eq, vecTensor_norm_eq,
    S.ψ_norm, seedResidueAncilla_norm, one_mul]

end

/-! ## From the seed-indexed game to the direct game -/

/-- The seed-indexed question selected in one residue block of a direct
question.  Applying `ldCL` ensures that irrelevant ambient coordinates are
canonicalized exactly as in the source game. -/
noncomputable def seededLdQuestion (L : LdParams)
    (q : DirectLdQuestion L.toDirectLdParams)
    (residue : SeedResidue L) : LdQuestion L :=
  (q.1, ldCL L q.1 (ldSpaceOfDirectResidue L q.2 residue))

section

variable (L : LdParams)
    (S : Strategy (ldGame L))
include L S

/-- Dilate a strategy for the seed-indexed low-degree game to the directly
indexed game.  The two local carriers receive correlated copies of the seed
residue, and each measurement is block diagonal in that residue. -/
noncomputable def ldStrategyToDirect : Strategy (directLdGame L.toDirectLdParams) where
  ιA := S.ιA × SeedResidue L
  ιB := S.ιB × SeedResidue L
  ψ := seedFiberLiftedState S L
  ψ_norm := seedFiberLiftedState_norm S L
  A q := blockDiagonalMeasurement fun residue =>
    matrixMeasurementTransport (ldDirectAnswerEquiv L)
      (S.A (seededLdQuestion L q residue))
  B q := blockDiagonalMeasurement fun residue =>
    matrixMeasurementTransport (ldDirectAnswerEquiv L)
      (S.B (seededLdQuestion L q residue))

/-- Projectivity is preserved by the correlated seed-fiber dilation. -/
theorem ldStrategyToDirect_isProjective (hS : S.IsProjective) :
    (ldStrategyToDirect L S).IsProjective := by
  constructor
  · intro q
    apply blockDiagonalMeasurement_isProjective
    intro residue
    apply matrixMeasurementTransport_isProjective
    exact hS.left (seededLdQuestion L q residue)
  · intro q
    apply blockDiagonalMeasurement_isProjective
    intro residue
    apply matrixMeasurementTransport_isProjective
    exact hS.right (seededLdQuestion L q residue)

end

/-- Coordinate formula for the correlated residue lift. -/
theorem seedFiberLiftedState_apply
    {G : Game} (S : Strategy G) (L : LdParams)
    (i : S.ιA) (j : S.ιB)
    (r s : SeedResidue L) :
    seedFiberLiftedState S L ((i, r), (j, s)) =
      if r = s then
        S.ψ (i, j) * (Real.sqrt (Fintype.card (SeedResidue L) : ℝ) : ℂ)⁻¹
      else 0 := by
  letI := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  simp [seedFiberLiftedState, reindexState, vecTensor, seedResidueAncilla,
    eprState, prodShuffle]

end

end MIPStarRE.QPBT
