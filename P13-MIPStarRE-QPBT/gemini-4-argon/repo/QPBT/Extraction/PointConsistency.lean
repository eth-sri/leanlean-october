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

/-- Placing a tensor with an identity on Bob's last register recovers `BB'`. -/
theorem placeSide_bob_tensor_one (S : ProjectiveSetting P epsilon)
    (B : Op (S.ExpandedLocalSpace .bob)) :
    S.placeSide .bob (heteroKron B (1 : Op (PauliRegister P))) = S.place .BB' B := by
  ext row col
  simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
    place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> rfl

/-- The point factor on `A` and the factors on `BB'B''` can be regrouped as
the factors on `BB'` and `AB''`, without moving any register. -/
theorem placePlayer_alice_mul_placeSide_bob_tensor (S : ProjectiveSetting P epsilon)
    (A : Op S.toStrategy.ιA) (B : Op (S.ExpandedLocalSpace .bob))
    (T : Op (PauliRegister P)) :
    S.placePlayer .alice A * S.placeSide .bob (heteroKron B T) =
      S.place .BB' B * S.place .AB'' (heteroKron A T) := by
  classical
  ext row col
  simp [placePlayer, placeSide, sixRegExtractionEquiv, reindexOp, heteroKron,
    Matrix.kronecker, place, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> ac_rfl

/-- Placing a tensor with an identity on Alice's last register recovers `AA'`. -/
theorem placeSide_alice_tensor_one (S : ProjectiveSetting P epsilon)
    (B : Op (S.ExpandedLocalSpace .alice)) :
    S.placeSide .alice (heteroKron B (1 : Op (PauliRegister P))) = S.place .AA' B := by
  ext row col
  simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
    place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite]
  split_ifs <;> rfl

/-- The factors on `AA'A''` and `B` can be regrouped on `AA'` and `BA''`
without exchanging registers or assuming symmetry of the strategy. -/
theorem placeSide_alice_tensor_mul_placePlayer_bob (S : ProjectiveSetting P epsilon)
    (B : Op (S.ExpandedLocalSpace .alice)) (T : Op (PauliRegister P))
    (A : Op S.toStrategy.ιB) :
    S.placeSide .alice (heteroKron B T) * S.placePlayer .bob A =
      S.place .AA' B * S.place .BA'' (heteroKron A T) := by
  classical
  ext row col
  simp [placePlayer, placeSide, sixRegExtractionEquiv, reindexOp, heteroKron,
    Matrix.kronecker, place, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> ac_rfl

/-- Extraction-block placement preserves finite sums. -/
theorem placeSide_finset_sum (S : ProjectiveSetting P epsilon) (side : PlayerSide)
    {I : Type*} (s : Finset I) (B : I → Op (ExtractionBlock P (S.LocalSpace side))) :
    S.placeSide side (∑ i ∈ s, B i) = ∑ i ∈ s, S.placeSide side (B i) := by
  classical
  cases side <;> {
    dsimp [placeSide]
    first | rw [heteroKron_finset_sum_left] | rw [heteroKron_finset_sum_right]
    ext; simp [reindexOp, Matrix.sum_apply] }

theorem placeSide_one (S : ProjectiveSetting P epsilon) (side : PlayerSide) :
    S.placeSide side 1 = 1 := by
  cases side <;> {
    dsimp [placeSide]; rw [heteroKron_one_one]; ext; simp [reindexOp, Matrix.one_apply] }

theorem placeSide_nonneg (S : ProjectiveSetting P epsilon) (side : PlayerSide)
    {B : Op (ExtractionBlock P (S.LocalSpace side))} (hB : 0 ≤ B) :
    0 ≤ S.placeSide side B := by
  cases side
  · exact reindexOp_nonneg _ (kronecker_nonneg hB Matrix.PosSemidef.one.nonneg)
  · exact reindexOp_nonneg _ (kronecker_nonneg Matrix.PosSemidef.one.nonneg hB)

theorem pointMeasExp_effect_eq_sum_sub (S : ProjectiveSetting P epsilon)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ∑ b : PauliScalar P, heteroKron ((S.pointMeas side W u).effect b)
        (tauDotProj W (indicatorVec u) (a - b)) := by
  classical
  change S.expPointOp side W u a = _
  rw [S.expPointOp_eq_convolution]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h (c : PauliScalar P) : b + c = a ↔ c = a - b := by rw [eq_sub_iff_add_eq, add_comm]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]; rfl

end ProjectiveSetting

theorem sum_pointMeas_mul_placeSide_bob_convolution
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (F : Poly P → PauliScalar P) :
    (∑ a : PauliScalar P, S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
      S.placeSide .bob (∑ g : Poly P, heteroKron ((w.marginalPoly .bob W).effect g)
        (tauDotProj W (indicatorVec u) (F g - a)))) =
      ∑ g : Poly P, S.place .BB' ((w.marginalPoly .bob W).effect g) *
        S.place .AB'' ((S.pointMeasExp .alice W u).effect (F g)) := by
  classical
  simp only [S.placeSide_finset_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [S.placePlayer_alice_mul_placeSide_bob_tensor, ← Finset.mul_sum,
    ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub .alice W u]

theorem sum_placeSide_alice_convolution_mul_pointMeas
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (F : Poly P → PauliScalar P) :
    (∑ a : PauliScalar P, S.placeSide .alice
      (∑ g : Poly P, heteroKron ((w.marginalPoly .alice W).effect g)
        (tauDotProj W (indicatorVec u) (F g - a))) *
      S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) =
      ∑ g : Poly P, S.place .AA' ((w.marginalPoly .alice W).effect g) *
        S.place .BA'' ((S.pointMeasExp .bob W u).effect (F g)) := by
  classical
  simp only [S.placeSide_finset_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [S.placeSide_alice_tensor_mul_placePlayer_bob, ← Finset.mul_sum,
    ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub .bob W u]

/-- The original/pulled-apart overlap is exactly the expanded-point overlap
at the decoded value. -/
theorem sum_pointMeas_mul_tildeM_eq_decoded_overlap
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
      S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) =
      ∑ g : Poly P, S.place .BB' ((w.marginalPoly .bob W).effect g) *
        S.place .AB'' ((S.pointMeasExp .alice W u).effect
          (dotProduct (decodeFq g) (indicatorVec u))) :=
  sum_pointMeas_mul_placeSide_bob_convolution w W u _

/-- The Alice-pulled/Bob-point overlap is exactly the expanded-point overlap
at the decoded value. -/
theorem sum_tildeM_mul_pointMeas_eq_decoded_overlap
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, S.placeSide .alice (tildeM w .alice W (indicatorVec u) a) *
      S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) =
      ∑ g : Poly P, S.place .AA' ((w.marginalPoly .alice W).effect g) *
        S.place .BA'' ((S.pointMeasExp .bob W u).effect
          (dotProduct (decodeFq g) (indicatorVec u))) :=
  sum_placeSide_alice_convolution_mul_pointMeas w W u _

private def placedTildeM {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P) (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  Measurement.ofSumEqOne
    (fun a => S.placeSide side (tildeM w side W (indicatorVec u) a))
    (fun a => S.placeSide_nonneg side (tildeM_isProj w side W (indicatorVec u) a).nonneg)
    (by rw [← S.placeSide_finset_sum, sum_tildeM_eq_one, S.placeSide_one])

/-- The pulled-apart consistency defect is one minus the decoded overlap. -/
theorem tildeM_consistencyDefect_eq_one_sub_decoded_overlap
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat =
      1 - avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        ∑ g : Poly P, stateQForm S.psiHat
          (S.place .BB' ((w.marginalPoly .bob W).effect g) *
            S.place .AB'' ((S.pointMeasExp .alice W u).effect
              (dotProduct (decodeFq g) (indicatorVec u))))) := by
  refine (consistencyDefect_eq_one_sub_overlap
    (uniformDistribution (Fin P.m → PauliScalar P))
    (fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u)))
    (placedTildeM w .bob W) S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm).trans
    (congrArg (1 - ·) (avgOver_congr _ _ _ fun u => ?_))
  change (∑ a : PauliScalar P, stateQForm S.psiHat
    (S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
      S.placeSide .bob (tildeM w .bob W (indicatorVec u) a))) = _
  rw [← stateQForm_finset_sum, sum_pointMeas_mul_tildeM_eq_decoded_overlap, stateQForm_finset_sum]

/-- The Alice-pulled/Bob-point consistency defect is one minus the decoded overlap. -/
theorem tildeM_consistencyDefect_eq_one_sub_decoded_overlap'
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat =
      1 - avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        ∑ g : Poly P, stateQForm S.psiHat
          (S.place .AA' ((w.marginalPoly .alice W).effect g) *
            S.place .BA'' ((S.pointMeasExp .bob W u).effect
              (dotProduct (decodeFq g) (indicatorVec u))))) := by
  refine (consistencyDefect_eq_one_sub_overlap
    (uniformDistribution (Fin P.m → PauliScalar P))
    (placedTildeM w .alice W)
    (fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))) S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm).trans
    (congrArg (1 - ·) (avgOver_congr _ _ _ fun u => ?_))
  change (∑ a : PauliScalar P, stateQForm S.psiHat
    (S.placeSide .alice (tildeM w .alice W (indicatorVec u) a) *
      S.placePlayer .bob ((S.pointMeas .bob W u).effect a))) = _
  rw [← stateQForm_finset_sum, sum_tildeM_mul_pointMeas_eq_decoded_overlap, stateQForm_finset_sum]

open scoped Classical in
/-- Replacing polynomial evaluation by decoded evaluation loses at most the
mass of the non-encoding outcomes. -/
theorem marginal_eval_overlap_le_decoded_add_nonencoding
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (∑ g : Poly P, stateQForm S.psiHat
      (S.place p1 ((w.marginalPoly p1.side W).effect g) *
        S.place p2 ((S.pointMeasExp p2.side W u).effect (MvPolynomial.eval u g.1)))) ≤
      (∑ g : Poly P, stateQForm S.psiHat
        (S.place p1 ((w.marginalPoly p1.side W).effect g) *
          S.place p2 ((S.pointMeasExp p2.side W u).effect
            (dotProduct (decodeFq g) (indicatorVec u))))) +
      ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place p1 ((w.marginalPoly p1.side W).effect g)) := by
  classical
  have hpos (g : Poly P) (a : PauliScalar P) :
      0 ≤ stateQForm S.psiHat
        (S.place p1 ((w.marginalPoly p1.side W).effect g) *
          S.place p2 ((S.pointMeasExp p2.side W u).effect a)) :=
    stateQForm_nonneg _ (S.place_mul_place_nonneg p1 p2 hopp
      ((w.marginalPoly p1.side W).pos g) ((S.pointMeasExp p2.side W u).pos a))
  have hsum (g : Poly P) :
      (∑ a : PauliScalar P, stateQForm S.psiHat
        (S.place p1 ((w.marginalPoly p1.side W).effect g) *
          S.place p2 ((S.pointMeasExp p2.side W u).effect a))) =
        stateQForm S.psiHat (S.place p1 ((w.marginalPoly p1.side W).effect g)) := by
    have hc : (∑ a : PauliScalar P,
        S.place p2 ((S.pointMeasExp p2.side W u).effect a)) = 1 :=
      (S.placedMeasurement p2 (S.pointMeasExp p2.side W u)).sum_eq_one
    rw [← stateQForm_finset_sum, ← Finset.mul_sum, hc, mul_one]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  by_cases hg : IsEncoding g
  · simp only [hg, not_true_eq_false, if_false, add_zero]
    rw [decodeFq_dotProduct_indicatorVec hg u]
    rfl
  · simp only [hg, not_false_eq_true, if_true]
    have hle := Finset.single_le_sum (fun a _ => hpos g a)
      (Finset.mem_univ (MvPolynomial.eval u g.1))
    rw [hsum] at hle
    exact hle.trans (le_add_of_nonneg_left (hpos g _))

end

end MIPStarRE.QPBT
