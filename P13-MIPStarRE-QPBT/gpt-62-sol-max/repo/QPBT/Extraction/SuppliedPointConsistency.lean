module

public import QPBT.Extraction.Consistency
public import QPBT.Extraction.PointConsistency
public import QPBT.Extraction.NonencodingSupport

/-!
# Supplied-witness point consistency for extraction

The two point estimates combine the point-consistency relations of a supplied
global polynomial-pair measurement with encoding support and polynomial
collision bounds.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
* `docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus ProjectiveSetting

noncomputable section

section

variable {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (w : GlobalPairWitness S δ)
include P ε δ S w

private theorem marginalReadoutDefect_eq (p q : Placement) (W : PauliKind)
    (f : (PauliPoint P) → Poly P → PauliScalar P) :
    marginalReadoutDefect w p q W f = 1 - avgOver (uniformDistribution _) (fun u =>
      marginalReadoutOverlap w p q W u (f u)) := by
  refine (consistencyDefect_eq_one_sub_overlap _ _ _ _
    (uniformDistribution_isProbability _) S.psiHat_norm).trans ?_
  congr 1
  refine avgOver_congr _ _ _ fun u => ?_
  simp only [placedMeasurement_effect, marginalReadoutOverlap, ← stateQForm_finset_sum,
    sum_marginalPoly_readout_mul]

private theorem marginalDecodedDefect_le {p : Placement}
    (hp : p.Primary) (W : PauliKind) :
    marginalReadoutDefect w p (overlapPartner p) W (fun u g => dotProduct (decodeFq g) (indicatorVec u)) ≤
      δ + nonencodingMarginalMass w p.side W := by
  classical
  have h := marginalPoly_pointMeas_consistent w hp W
  rw [marginalReadoutDefect_eq] at h ⊢
  have hpq := p.opposite_partner
  have hcompare := avgOver_mono (uniformDistribution _) _ _ (fun u =>
    marginal_eval_overlap_le_decoded_add_nonencoding w p (overlapPartner p) hpq W u)
  rw [avgOver_add, avgOver_const_of_isProbability _ (uniformDistribution_isProbability _)] at hcompare
  have hm : (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm S.psiHat (S.place p ((w.marginalPoly p.side W).effect g))) =
      nonencodingMarginalMass w p.side W := by
    cases hp <;> simp only [nonencodingMarginalMass,
      S.placeSide_alice_tensor_one, S.placeSide_bob_tensor_one] <;> rfl
  rw [hm] at hcompare
  change _ - avgOver _ (fun u => marginalReadoutOverlap w p (overlapPartner p) W u
    (fun g => MvPolynomial.eval u g.1)) ≤ _ at h
  linarith

end

private theorem absorb_nonencoding {P : AdmissibleParams} {ε δ mass defect : ℝ}
    (hδ : 0 ≤ δ) (h : defect ≤ δ + mass)
    (hm : mass ≤ δ + (1 + 2 * Real.sqrt 172) * Real.sqrt ε + (P.m * P.d : ℝ) / P.q) :
    defect ≤ deltaConstructPaulis (2 + 2 * Real.sqrt 172) ε δ P.m P.d P.q := by
  unfold deltaConstructPaulis
  rw [Nat.cast_mul]
  have hr : 0 ≤ (P.m * P.d : ℝ) / P.q := by positivity
  nlinarith [Real.sqrt_nonneg ε, Real.sqrt_nonneg (172 : ℝ)]

/-- The decoded pulled-apart measurement is consistent with the other player's original points. -/
theorem tilde_point_defect_le {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (w : GlobalPairWitness S δ) {p : Placement}
    (hp : p.Primary) (W : PauliKind) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    measurementDefect (uniformDistribution (PauliPoint P))
      (fun u => S.blockMeasurement p.side (tildeMMeasurement w p.side W (indicatorVec u)))
      (fun u => S.playerMeasurement (overlapPartner p).side (S.pointMeas (overlapPartner p).side W u))
      S.psiHat ≤ deltaConstructPaulis (2 + 2 * Real.sqrt 172) ε δ P.m P.d P.q := by
  classical
  rw [pullingReadout_defect_eq w hp W _ _ (fun u a => tildeM_eq_sum w p.side W (indicatorVec u) a)]
  refine absorb_nonencoding hδ (marginalDecodedDefect_le w hp W) ?_
  have href := global_marginal_encoding_consistency_explicit P ε δ hε S w W
  have hψ := ExtendedLineGame.pairState_norm S
  cases hp
  · have hm := mass_outside_encoding_le_evaluated_defect (w.marginalPoly .alice W)
      (S.encodingPauliMeas .bob W) _ hψ (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .bob W)
    simp only [nonencodingMarginalMass, Placement.side]
    simp_rw [stateQForm_placeSide_alice_tensor_one S]
    exact hm.trans (add_le_add href.1 le_rfl)
  · have hm := right_mass_outside_encoding_le_evaluated_defect (S.encodingPauliMeas .alice W)
      (w.marginalPoly .bob W) _ hψ (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .alice W)
    simp only [nonencodingMarginalMass, Placement.side]
    simp_rw [stateQForm_placeSide_bob_tensor_one S]
    exact hm.trans (add_le_add href.2 le_rfl)

end

end MIPStarRE.QPBT
