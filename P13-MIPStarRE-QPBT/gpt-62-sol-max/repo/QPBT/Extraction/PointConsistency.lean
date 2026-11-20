module

public import QPBT.Extraction.BlockMeasurement
public import QPBT.Observables.LineMeasurement
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
open MIPStarRE.Quantum DistanceCalculus ProjectiveSetting

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ}

/-- Move the ancillary factor of the pulled measurement next to the opposite point. -/
theorem placeSide_tensor_mul_placePlayer (S : ProjectiveSetting P epsilon)
    {p : Placement} (hp : p.Primary) (B : Op (S.ExpandedLocalSpace p.side))
    (A : Op (S.LocalSpace (overlapPartner p).side)) (T : Op (PauliRegister P)) :
    S.placeSide p.side (heteroKron B T) * S.placePlayer (overlapPartner p).side A =
      S.place p B * S.place (overlapPartner p) (heteroKron A T) := by
  classical
  cases hp <;> simp only [placePlayer, overlapPartner]
  all_goals
    rw [place_eq_reindex, place_eq_reindex, place_eq_reindex]
    ext row col
    simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
      placeSplit, swapPaired, aaBaBipartition, abBbBipartition, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul] <;> split_ifs <;> ac_rfl

/-- The convolution formula with its second outcome solved for. This is the
third line of the overlap calculation in paper lines 1483--1492. -/
theorem pointMeasExp_effect_eq_sum_sub (S : ProjectiveSetting P epsilon)
    (side : PlayerSide) (W : PauliKind) (u : PauliPoint P)
    (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ∑ b : PauliScalar P, heteroKron ((S.pointMeas side W u).effect b)
        (tauDotProj W (indicatorVec u) (a - b)) := by
  classical
  change S.expPointOp side W u a = _
  rw [S.expPointOp_eq_convolution]
  simp [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  have h (c : PauliScalar P) : b + c = a ↔ c = a - b := by
    rw [eq_sub_iff_add_eq, add_comm]
  simp [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

end ProjectiveSetting

section

variable {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (w : GlobalPairWitness S δ)
include P ε δ S w

/-- The subtraction convolution can be read on the opposite expanded points
without changing the point consistency defect. This applies both to evaluation
of the difference polynomial and to reading its decoded label. -/
theorem pullingReadout_defect_eq {p : Placement}
    (hp : p.Primary) (W : PauliKind)
    (f : (PauliPoint P) → Poly P → PauliScalar P)
    (N : (PauliPoint P) → Measurement (PauliScalar P) (ExtractionBlock P (S.LocalSpace p.side)))
    (hN : ∀ u a, (N u).effect a = ∑ g, heteroKron ((w.marginalPoly p.side W).effect g)
      (tauDotProj W (indicatorVec u) (f u g - a))) :
    measurementDefect (uniformDistribution (PauliPoint P))
      (fun u => S.blockMeasurement p.side (N u))
      (fun u => S.playerMeasurement (overlapPartner p).side (S.pointMeas (overlapPartner p).side W u))
      S.psiHat = marginalReadoutDefect w p (overlapPartner p) W f := by
  refine measurementDefect_eq_of_overlap _ _ _ _ _ _ fun u => ?_
  simp only [blockMeasurement_effect, playerMeasurement_effect, placedMeasurement_effect,
    hN, S.placeSide_finset_sum, Finset.sum_mul]
  rw [Finset.sum_comm, sum_marginalPoly_readout_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [S.placeSide_tensor_mul_placePlayer hp]
  rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub]

/-- The overlap of a marginal readout with the opposite expanded point. -/
abbrev marginalReadoutOverlap (p q : Placement) (W : PauliKind)
    (u : PauliPoint P) (label : Poly P → PauliScalar P) : ℝ :=
  ∑ g, S.placedCorrelation p q
    ((w.marginalPoly p.side W).effect g) ((S.pointMeasExp q.side W u).effect (label g))

open scoped Classical in
/-- Changing from evaluation to the decoder can lose only the non-encoding
mass, regardless of the directed pair of placements. -/
theorem marginal_eval_overlap_le_decoded_add_nonencoding (p q : Placement) (hpq : p.IsOpposite q)
    (W : PauliKind) (u : PauliPoint P) :
    marginalReadoutOverlap w p q W u (fun g => MvPolynomial.eval u g.1) ≤
      marginalReadoutOverlap w p q W u (fun g => dotProduct (decodeFq g) (indicatorVec u)) +
      ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place p ((w.marginalPoly p.side W).effect g)) := by
  classical
  let E (g : Poly P) (a : PauliScalar P) := S.placedCorrelation p q
    ((w.marginalPoly p.side W).effect g) ((S.pointMeasExp q.side W u).effect a)
  have hpos g a : 0 ≤ E g a := stateQForm_nonneg _ (S.place_mul_place_nonneg p q hpq
    ((w.marginalPoly p.side W).pos g) ((S.pointMeasExp q.side W u).pos a))
  have hsum g : ∑ a, E g a = stateQForm S.psiHat (S.place p ((w.marginalPoly p.side W).effect g)) := by
    dsimp only [E]
    rw [← stateQForm_finset_sum, ← Finset.mul_sum,
      ← S.place_finset_sum, (S.pointMeasExp q.side W u).sum_eq_one, S.place_one, mul_one]
  unfold marginalReadoutOverlap
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun g _ => ?_
  change E g (MvPolynomial.eval u g.1) ≤ E g _ + _
  by_cases hg : IsEncoding g
  · simp only [hg, not_true_eq_false, ite_false, add_zero]
    change E g (evalPoly g u) ≤ E g (dotProduct (decodeFq g) (indicatorVec u))
    rw [decodeFq_dotProduct_indicatorVec hg u]
  · simp only [hg, not_false_eq_true, ite_true]
    rw [← hsum]
    exact (Finset.single_le_sum (fun a _ => hpos g a) (Finset.mem_univ _)).trans
      (le_add_of_nonneg_left (hpos g _))


end

end

end MIPStarRE.QPBT
