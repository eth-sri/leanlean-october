module

public import QPBT.Combining.DirectLowDegree.Transport.Strategy
public import QPBT.Games.DistanceTheorems.LdtBridge

/-!
# Low-degree consistency transport

This module identifies the low individual degree polynomial outcomes with the
bounded polynomial representatives used by the directly indexed QPBT game.  It
also transports complete measurements and their evaluation postprocessings
without changing either coordinate order or consistency error.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-! ## Polynomial outcomes -/

private theorem directPolynomialRename_degreeOf_le
    (D : DirectLdParams) (p : MvPolynomial (Fin D.m) (DirectScalarQ D))
    (hp : ∀ i, MvPolynomial.degreeOf i p ≤ D.d) (i : Fin D.m) :
    MvPolynomial.degreeOf i (MvPolynomial.rename Fin.rev p) ≤ D.d := by
  rw [← Fin.rev_rev i,
    MvPolynomial.degreeOf_rename_of_injective Fin.rev_injective]
  exact hp (Fin.rev i)

private theorem ldtPolynomial_ext
    {params : Parameters} [FieldModel params.q]
    {g h : MIPStarRE.LDT.Polynomial params} (hpoly : g.poly = h.poly) : g = h := by
  cases g with
  | mk gp hg =>
      simp_all

/-- Bounded QPBT polynomial representatives are equivalent to LDT
polynomial outcomes.  The variable renaming is the same coordinate reversal
as `directPointEquiv`, so evaluation retains the direct coordinate order. -/
noncomputable def directPolyEquivPolynomial (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    DirectPolynomial D ≃
      MIPStarRE.LDT.Polynomial D.toLDTParameters := by
  letI := D.toLDTFieldModel
  refine
    { toFun := fun g =>
        { poly := MvPolynomial.rename Fin.rev g.1
          lowIndividualDegree := by
            exact directPolynomialRename_degreeOf_le D g.1
              (degreeOf_le_of_mem_polyFunc g.2) }
      invFun := fun g =>
        ⟨MvPolynomial.rename Fin.rev g.poly, by
          rw [MvPolynomial.mem_restrictDegree]
          intro s hs i
          exact (MvPolynomial.degreeOf_le_iff.mp (by
            exact directPolynomialRename_degreeOf_le D g.poly
              g.lowIndividualDegree i)) s hs⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro g
    apply Subtype.ext
    change MvPolynomial.rename Fin.rev
      (MvPolynomial.rename Fin.rev g.1) = g.1
    rw [MvPolynomial.rename_rename]
    rw [show Fin.rev ∘ Fin.rev = id by funext i; simp]
    exact MvPolynomial.rename_id_apply g.1
  · intro g
    cases g with
    | mk p hp =>
        have hpoly : MvPolynomial.rename Fin.rev
            (MvPolynomial.rename Fin.rev p) = p := by
          rw [MvPolynomial.rename_rename]
          rw [show Fin.rev ∘ Fin.rev = id by funext i; simp]
          exact MvPolynomial.rename_id_apply p
        exact (by
          exact ldtPolynomial_ext hpoly)

@[simp] theorem directPolyEquivPolynomial_poly
    (D : DirectLdParams) (g : DirectPolynomial D) :
    letI := D.toLDTFieldModel
    (directPolyEquivPolynomial D g).poly = MvPolynomial.rename Fin.rev g.1 := by
  letI := D.toLDTFieldModel
  rfl

/-- The polynomial equivalence commutes with evaluation after the direct point
and scalar codings. -/
@[simp] theorem directPolyEquivPolynomial_apply
    (D : DirectLdParams) (g : DirectPolynomial D)
    (u : DirectPoint D) :
    letI := D.toLDTFieldModel
    directPolyEquivPolynomial D g (directPointEquiv D u) =
      directScalarEquiv D (MvPolynomial.eval u g.1) := by
  letI := D.toLDTFieldModel
  unfold MIPStarRE.LDT.Polynomial.toFun evalPolynomialModel
  rw [directPolyEquivPolynomial_poly]
  unfold decodePoint
  rw [MvPolynomial.eval_rename]
  congr 1
  apply congrArg (fun v : DirectPoint D =>
    MvPolynomial.eval v g.1)
  funext i
  simp only [Function.comp_apply, directPointEquiv_apply, Fin.rev_rev]
  change (directScalarEquiv D).symm (directScalarEquiv D (u i)) = u i
  exact (directScalarEquiv D).symm_apply_apply (u i)

/-! ## Complete measurements -/

/-- Relabel an LDT polynomial projective measurement by direct QPBT
polynomial representatives. -/
noncomputable def directPolynomialMeasurement
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    {iota : Type*} → [Fintype iota] → [DecidableEq iota] →
      ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota →
        PolyMeas D.m (DirectScalarQ D) D.d iota := by
  letI := D.toLDTFieldModel
  intro iota _ _ G
  exact matrixMeasurementTransport (directPolyEquivPolynomial D).symm
    (ldtMeasurementToMatrixMeasurement G.toMeasurement)

@[simp] theorem directPolynomialMeasurement_effect
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {iota : Type*} [Fintype iota] [DecidableEq iota]
      (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota)
      (g : DirectPolynomial D),
      (directPolynomialMeasurement D G).effect g =
        G.outcome (directPolyEquivPolynomial D g) := by
  letI := D.toLDTFieldModel
  intro iota _ _ G g
  rfl

/-- Evaluating the transported polynomial measurement is the relabeling of
the LDT evaluation postprocessing through `directScalarEquiv`. -/
theorem directPolynomialMeasurement_evaluation_effect
    (D : DirectLdParams) :
    letI := D.toLDTFieldModel
    ∀ {iota : Type*} [Fintype iota] [DecidableEq iota]
      (G : ProjMeas (MIPStarRE.LDT.Polynomial D.toLDTParameters) iota)
      (u : DirectPoint D) (a : DirectScalarQ D),
      ((directPolynomialMeasurement D G).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a =
        (ldtMeasurementToMatrixMeasurement
          (ProjMeas.postprocess G
            (fun g => g (directPointEquiv D u))).toMeasurement).effect
            (directScalarEquiv D a) := by
  letI := D.toLDTFieldModel
  intro iota _ _ G u a
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [ldtMeasurementToMatrixMeasurement_effect,
    ProjMeas.postprocess, SubMeas.postprocess_outcome]
  simp only [Finset.sum_filter]
  refine Fintype.sum_equiv (directPolyEquivPolynomial D) _ _ fun g => ?_
  rw [directPolynomialMeasurement_effect, directPolyEquivPolynomial_apply]
  simp

/-! ## Correlated-ancilla compression -/

/-!
The diagonal-block conditional expectation preserves either mixed defect
exactly because the point measurement on the opposite carrier is constant on
the residue register.  It does not yield a global/global compression theorem:
the lifted state pairs equal residues, whereas separately compressing both
polynomial measurements produces an independent double average over residues.
Neither quantity bounds the other in general.  This open obstruction is
recorded in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

/-- The normalized diagonal-block average of an operator on a carrier with a
finite ancillary register.  This is the local conditional expectation used to
discard one half of the correlated seed-residue ancilla. -/
noncomputable def averageDiagonalBlock
    {iota block : Type*} [Fintype iota] [Fintype block] :
    Op (iota × block) →ₗ[ℝ] Op iota where
  toFun A := (Fintype.card block : ℝ)⁻¹ • ∑ r, A.submatrix (fun i => (i, r)) (fun i => (i, r))
  map_add' A B := by simp [Matrix.submatrix_add, Finset.sum_add_distrib, smul_add]
  map_smul' c A := by
    simp only [RingHom.id_apply, Matrix.submatrix_smul, Pi.smul_apply, ← Finset.smul_sum,
      smul_comm c]

theorem averageDiagonalBlock_apply {iota block : Type*} [Fintype iota] [Fintype block]
    (A : Op (iota × block)) : averageDiagonalBlock A =
      (Fintype.card block : ℝ)⁻¹ • ∑ r, A.submatrix (fun i => (i, r)) (fun i => (i, r)) := rfl

/-- Averaging a constant block amplification recovers its original operator. -/
theorem averageDiagonalBlock_blockDiagonal_const
    {iota block : Type*} [Fintype iota]
    [Fintype block] [DecidableEq block] [Nonempty block] (M : Op iota) :
    averageDiagonalBlock (Matrix.blockDiagonal fun _ : block => M) = M := by
  classical
  have h (r : block) : (Matrix.blockDiagonal fun _ : block => M).submatrix
      (fun i => (i, r)) (fun i => (i, r)) = M :=
    Matrix.ext fun i j => Matrix.blockDiagonal_apply_eq (fun _ => M) i j r
  simp only [averageDiagonalBlock_apply, h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- Compress a POVM through the normalized diagonal-block average.  The
nonemptiness assumption says precisely that the normalized finite average is
defined over at least one ancillary basis element. -/
noncomputable def correlatedAncillaCompressMeasurement
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : MIPStarRE.Quantum.Measurement alpha (iota × block)) :
    MIPStarRE.Quantum.Measurement alpha iota :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => averageDiagonalBlock (M.effect a))
    (fun a => by
      rw [averageDiagonalBlock_apply]
      apply smul_nonneg
      · positivity
      · exact Finset.sum_nonneg fun r _ =>
          Matrix.nonneg_iff_posSemidef.mpr
            ((Matrix.nonneg_iff_posSemidef.mp (M.pos a)).submatrix
              (fun i => (i, r))))
    (by
      rw [← map_sum, M.sum_eq_one, ← Matrix.blockDiagonal_one]
      exact averageDiagonalBlock_blockDiagonal_const (block := block) 1)

@[simp] theorem correlatedAncillaCompressMeasurement_effect
    {alpha iota block : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : MIPStarRE.Quantum.Measurement alpha (iota × block)) (a : alpha) :
    (correlatedAncillaCompressMeasurement M).effect a =
      averageDiagonalBlock (M.effect a) :=
  rfl

/-- Normalized diagonal-block compression commutes with deterministic outcome
postprocessing. -/
theorem correlatedAncillaCompressMeasurement_postprocess
    {alpha beta iota block : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block] [Nonempty block]
    (M : MIPStarRE.Quantum.Measurement alpha (iota × block))
    (f : alpha → beta) :
    correlatedAncillaCompressMeasurement (M.postprocess f) =
      (correlatedAncillaCompressMeasurement M).postprocess f := by
  classical
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
    correlatedAncillaCompressMeasurement_effect,
    MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact map_sum averageDiagonalBlock M.effect _

/-- Specialize ancillary compression to the nonempty residue fiber supplied by
the divisibility data of `LdParams`. -/
noncomputable def seedFiberCompressMeasurement
    (L : LdParams) {alpha iota : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha
      (iota × SeedResidue L)) :
    MIPStarRE.Quantum.Measurement alpha iota := by
  letI :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact correlatedAncillaCompressMeasurement M

@[simp] theorem seedFiberCompressMeasurement_effect
    (L : LdParams) {alpha iota : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha
      (iota × SeedResidue L)) (a : alpha) :
    (seedFiberCompressMeasurement L M).effect a =
      averageDiagonalBlock (M.effect a) :=
  rfl

/-- Seed-fiber compression commutes with deterministic outcome
postprocessing. -/
theorem seedFiberCompressMeasurement_postprocess
    (L : LdParams) {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (M : MIPStarRE.Quantum.Measurement alpha
      (iota × SeedResidue L)) (f : alpha → beta) :
    seedFiberCompressMeasurement L (M.postprocess f) =
      (seedFiberCompressMeasurement L M).postprocess f := by
  letI :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact correlatedAncillaCompressMeasurement_postprocess M f

/-- Compress a direct polynomial-tuple POVM from the correlated seed-residue
carrier to the corresponding seed-indexed polynomial POVM. -/
noncomputable def seedFiberCompressPolyMeasTuple
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple L.toDirectLdParams
      (iota × SeedResidue L)) : PolyMeasTuple L iota := seedFiberCompressMeasurement L G

/-- Polynomial evaluation commutes exactly with compression of the correlated
seed-residue carrier. -/
theorem seedFiberCompressPolyMeasTuple_evaluation
    (L : LdParams) {iota : Type*} [Fintype iota] [DecidableEq iota]
    (G : DirectPolyMeasTuple L.toDirectLdParams
      (iota × SeedResidue L)) (u : LdPoint L) :
    (seedFiberCompressPolyMeasTuple L G).postprocess (evalPolyTupleAt u) =
      seedFiberCompressMeasurement L
        (G.postprocess (evalDirectPolyTupleAt u)) := by
  exact (seedFiberCompressMeasurement_postprocess L G
    (evalDirectPolyTupleAt u)).symm

/-- Block-diagonal assembly commutes with deterministic outcome
postprocessing. -/
theorem blockDiagonalMeasurement_postprocess
    {alpha beta iota block : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    [Fintype block] [DecidableEq block]
    (M : block → MIPStarRE.Quantum.Measurement alpha iota)
    (f : alpha → beta) :
    (blockDiagonalMeasurement M).postprocess f =
      blockDiagonalMeasurement (fun r => (M r).postprocess f) := by
  classical
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, blockDiagonalMeasurement_effect,
    blockDiagonal_finset_sum]

private theorem matrixMeasurementTransport_eq_postprocess
    {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota) :
    matrixMeasurementTransport e M = M.postprocess e := by
  classical
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [Finset.sum_eq_single (e.symm b)]
  · rfl
  · intro a haMem ha
    have hea := (Finset.mem_filter.mp haMem).2
    exact (ha (e.injective (hea.trans (e.apply_symm_apply b).symm))).elim
  · simp

/-- Relabeling along an outcome equivalence commutes with subsequent
postprocessing. -/
theorem matrixMeasurementTransport_postprocess
    {alpha beta gamma iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma]
    [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : MIPStarRE.Quantum.Measurement alpha iota)
    (f : beta → gamma) :
    (matrixMeasurementTransport e M).postprocess f =
      M.postprocess (fun a => f (e a)) := by
  rw [matrixMeasurementTransport_eq_postprocess,
    MIPStarRE.Quantum.Measurement.postprocess_comp]

end

end MIPStarRE.QPBT
