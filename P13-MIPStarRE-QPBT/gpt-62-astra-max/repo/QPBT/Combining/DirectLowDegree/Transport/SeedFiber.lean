module

public import QPBT.Combining.DirectLowDegree.Transport.Correspondence

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

variable {alpha beta iota block : Type*} [Fintype alpha] [Fintype beta] [Fintype iota]
  [DecidableEq iota] [Fintype block] [DecidableEq block] (e : alpha ≃ beta)
  (M : block → MIPStarRE.Quantum.Measurement alpha iota)

/-- Relabel a matrix measurement along an equivalence of outcome alphabets. -/
noncomputable def matrixMeasurementTransport (M : MIPStarRE.Quantum.Measurement alpha iota) :
    MIPStarRE.Quantum.Measurement beta iota :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun b => M.effect (e.symm b))
    (fun b => M.pos (e.symm b))
    (by
      rw [← M.sum_eq_one]
      exact Equiv.sum_comp e.symm M.effect)

/-- Relabeling a projective matrix measurement preserves projectivity. -/
theorem matrixMeasurementTransport_isProjective (M : MIPStarRE.Quantum.Measurement alpha iota)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (matrixMeasurementTransport e M) :=
  fun b => hM (e.symm b)

/-- Assemble a family of matrix measurements as diagonal blocks indexed by a
finite classical register. -/
noncomputable def blockDiagonalMeasurement :
    MIPStarRE.Quantum.Measurement alpha (iota × block) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => Matrix.blockDiagonal fun r => (M r).effect a)
    (fun a => Matrix.blockDiagonal_nonneg
      (fun r => (M r).effect a) (fun r => (M r).pos a))
    (by
      ext ⟨i, r⟩ ⟨j, s⟩
      simp only [Matrix.sum_apply, Matrix.blockDiagonal_apply]
      by_cases hrs : r = s
      · subst s
        simp only [if_pos]
        calc
          _ = (1 : Matrix iota iota ℂ) i j :=
            by
              simpa only [Matrix.sum_apply] using
                congrFun (congrFun (M r).sum_eq_one i) j
          _ = _ := by
                change (if i = j then 1 else 0) =
                  (if (i, r) = (j, r) then 1 else 0)
                simp
      · simp [hrs])

@[simp] theorem blockDiagonalMeasurement_effect
    (a : alpha) :
    (blockDiagonalMeasurement M).effect a =
      Matrix.blockDiagonal (fun r => (M r).effect a) :=
  rfl

/-- A block-diagonal family of projective measurements is projective. -/
theorem blockDiagonalMeasurement_isProjective
    (hM : ∀ r, MIPStarRE.QPBT.Measurement.IsProjective (M r)) :
    MIPStarRE.QPBT.Measurement.IsProjective (blockDiagonalMeasurement M) := by
  intro a
  constructor
  · change Matrix.blockDiagonal _ *
        Matrix.blockDiagonal (fun r => (M r).effect a) =
      Matrix.blockDiagonal (fun r => (M r).effect a)
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext r
    exact (hM r a).isIdempotentElem.eq
  · change (Matrix.blockDiagonal (fun r => (M r).effect a))ᴴ =
      _
    simp
    congr 1
    funext r
    exact (hM r a).isSelfAdjoint.star_eq

end

/-! ## The correlated residue state -/

variable {G : Game} (S : Strategy G) (L : LdParams)

/-- The normalized maximally correlated state on the common seed-fiber
residue. -/
noncomputable def seedResidueAncilla :
    EuclideanSpace ℂ
      (Fin (L.q / L.m) × Fin (L.q / L.m)) := by
  letI :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact eprState (Fin (L.q / L.m))

/-- The seed-residue ancilla has unit norm. -/
theorem seedResidueAncilla_norm :
    ‖seedResidueAncilla L‖ = 1 := by
  letI :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  apply eprState_norm

/-- Tensor the original strategy state with the maximally correlated residue
state and shuffle the factors back into the two local carriers. -/
noncomputable def seedFiberLiftedState :
    EuclideanSpace ℂ
      ((S.ιA × Fin (L.q / L.m)) × (S.ιB × Fin (L.q / L.m))) :=
  reindexState prodShuffle (vecTensor S.ψ (seedResidueAncilla L))

/-! ## From the seed-indexed game to the direct game -/

/-- The seed-indexed question selected in one residue block of a direct
question.  Applying `ldCL` ensures that irrelevant ambient coordinates are
canonicalized exactly as in the source game. -/
noncomputable def seededLdQuestion
    (q : DirectLdQuestion L.toDirectLdParams)
    (residue : Fin (L.q / L.m)) : LdQuestion L :=
  (q.1, ldCL L q.1 (ldSpaceOfDirectResidue q.2 residue))

variable {L} in
/-- Dilate a strategy for the seed-indexed low-degree game to the directly
indexed game.  The two local carriers receive correlated copies of the seed
residue, and each measurement is block diagonal in that residue. -/
noncomputable def ldStrategyToDirect
    (S : Strategy (ldGame L)) : Strategy (directLdGame L.toDirectLdParams) where
  ιA := S.ιA × Fin (L.q / L.m)
  ιB := S.ιB × Fin (L.q / L.m)
  ψ := seedFiberLiftedState S L
  ψ_norm := (by
              rw [seedFiberLiftedState, reindexState_norm_eq, vecTensor_norm_eq,
                S.ψ_norm, seedResidueAncilla_norm, one_mul])
  A q := blockDiagonalMeasurement fun residue =>
    matrixMeasurementTransport (ldDirectAnswerEquiv L)
      (S.A (seededLdQuestion L q residue))
  B q := blockDiagonalMeasurement fun residue =>
    matrixMeasurementTransport (ldDirectAnswerEquiv L)
      (S.B (seededLdQuestion L q residue))

/-- Projectivity is preserved by the correlated seed-fiber dilation. -/
theorem ldStrategyToDirect_isProjective
    (S : Strategy (ldGame L)) (hS : S.IsProjective) :
    (ldStrategyToDirect S).IsProjective := by
  constructor
  · intro q
    apply blockDiagonalMeasurement_isProjective
    intro residue
    apply matrixMeasurementTransport_isProjective
    apply hS.1
  · intro q
    apply blockDiagonalMeasurement_isProjective
    intro residue
    apply matrixMeasurementTransport_isProjective
    apply hS.2

/-- Coordinate formula for the correlated residue lift. -/
theorem seedFiberLiftedState_apply
    (i : S.ιA) (j : S.ιB)
    (r s : Fin (L.q / L.m)) :
    seedFiberLiftedState S L ((i, r), (j, s)) =
      if r = s then
        S.ψ (i, j) * (Real.sqrt (Fintype.card (Fin (L.q / L.m)) : ℝ) : ℂ)⁻¹
      else 0 := by
  letI :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  simp [seedFiberLiftedState, reindexState, vecTensor, seedResidueAncilla,
    eprState, prodShuffle]

end

end MIPStarRE.QPBT
