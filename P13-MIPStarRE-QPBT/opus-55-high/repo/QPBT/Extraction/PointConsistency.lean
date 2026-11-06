module

public import QPBT.Extraction.Observables
public import QPBT.Combining.Points.PlacementSupport
public import QPBT.Combining.Lines.ConsistencyPositivity

/-!
# Point consistency after decoding polynomial outcomes

This module expands the overlap of an original point measurement with a
pulled-apart measurement. The decoded polynomial is kept explicit, so the
calculation does not use the decoder identity outside the encoding image.

## References

These are auxiliary identities for blueprint `lem:qld-construct-the-paulis`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`.
The restriction on the decoder identity is recorded in
`docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ}

variable (S : ProjectiveSetting P epsilon)

/-- Placing a tensor with an identity on Bob's last register recovers `BB'`. -/
theorem placeSide_bob_tensor_one (B : Op (S.ExpandedLocalSpace .bob)) :
    S.placeSide .bob (heteroKron B (1 : Op (PauliRegister P))) = S.place .BB' B := by
  ext row col
  simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
    place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  grind

/-- The point factor on `A` and the factors on `BB'B''` can be regrouped as
the factors on `BB'` and `AB''`, without moving any register. -/
theorem placePlayer_alice_mul_placeSide_bob_tensor (A : Op S.toStrategy.ιA) (B : Op (S.ExpandedLocalSpace .bob))
    (T : Op (PauliRegister P)) :
    S.placePlayer .alice A * S.placeSide .bob (heteroKron B T) =
      S.place .BB' B * S.place .AB'' (heteroKron A T) := by
  ext row col
  simp [placePlayer, placeSide, sixRegExtractionEquiv, reindexOp, heteroKron,
    Matrix.kronecker, place, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  grind

/-- Bob's extraction-block placement preserves finite sums. -/
theorem placeSide_bob_finset_sum {I : Type*} (s : Finset I) (B : I → Op (ExtractionBlock P S.toStrategy.ιB)) :
    S.placeSide .bob (∑ i ∈ s, B i) = ∑ i ∈ s, S.placeSide .bob (B i) := by
  change reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
    (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA)) (∑ i ∈ s, B i)) = _
  rw [heteroKron_finset_sum_right]
  ext row col
  simp [placeSide, reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]

/-- The convolution formula with its second outcome solved for. This is the
third line of the overlap calculation in paper lines 1483--1492. -/
theorem pointMeasExp_effect_eq_sum_sub (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ∑ b : PauliScalar P, heteroKron ((S.pointMeas side W u).effect b)
        (tauDotProj W (indicatorVec u) (a - b)) := by
  change S.expPointOp side W u a = _
  rw [S.expPointOp_eq_convolution]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  have h (c : PauliScalar P) : b + c = a ↔ c = a - b := by
    rw [eq_sub_iff_add_eq, add_comm]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

end ProjectiveSetting

variable {P : AdmissibleParams} {epsilon deltaG : ℝ}

/-- The original/pulled-apart overlap is exactly the expanded-point overlap
at the decoded value. This is the first three lines of the proof of Item 1 in
paper lines 1483--1492; it holds for every polynomial outcome. -/
theorem sum_pointMeas_mul_tildeM_eq_decoded_overlap
    {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
      S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) =
      ∑ g : Poly P, S.place .BB' ((w.marginalPoly .bob W).effect g) *
        S.place .AB'' ((S.pointMeasExp .alice W u).effect
          (dotProduct (decodeFq g) (indicatorVec u))) := by
  simp only [tildeM, S.placeSide_bob_finset_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [S.placePlayer_alice_mul_placeSide_bob_tensor]
  rw [← Finset.mul_sum, ← S.place_finset_sum,
    S.pointMeasExp_effect_eq_sum_sub .alice W u]

/-- The pulled-apart consistency defect is one minus the decoded overlap.
This combines completeness with the first three lines of the source's
calculation, still without imposing an encoding restriction. -/
theorem tildeM_consistencyDefect_eq_one_sub_decoded_overlap
    {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat =
      1 - avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        ∑ g : Poly P, stateQForm S.psiHat
          (S.place .BB' ((w.marginalPoly .bob W).effect g) *
            S.place .AB'' ((S.pointMeasExp .alice W u).effect
              (dotProduct (decodeFq g) (indicatorVec u))))) := by
  let point := fun u : Fin P.m → PauliScalar P =>
    S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u))
  let pulled := fun u =>
    Measurement.ofSumEqOne
      (fun a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a))
      (fun a => by
        apply ProjectiveSetting.reindexOp_nonneg
        exact kronecker_nonneg Matrix.PosSemidef.one.nonneg
          (tildeM_isProj w .bob W (indicatorVec u) a).nonneg)
      (by
        rw [← S.placeSide_bob_finset_sum, sum_tildeM_eq_one]
        change reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
            (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
        simp [heteroKron_one_one, reindexOp])
  have h := consistencyDefect_eq_one_sub_overlap
    (uniformDistribution (Fin P.m → PauliScalar P)) point pulled S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  change consistencyDefect _ _ _ S.psiHat = 1 - avgOver _ (fun u =>
    ∑ a : PauliScalar P, stateQForm S.psiHat
      (S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
        S.placeSide .bob (tildeM w .bob W (indicatorVec u) a))) at h
  refine h.trans ?_
  congr 1
  apply avgOver_congr
  intro u
  rw [← stateQForm_finset_sum, sum_pointMeas_mul_tildeM_eq_decoded_overlap,
    stateQForm_finset_sum]

end

end MIPStarRE.QPBT
