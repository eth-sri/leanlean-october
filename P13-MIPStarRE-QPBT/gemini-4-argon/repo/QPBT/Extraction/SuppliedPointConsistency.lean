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
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

open scoped Classical in
private theorem decoded_overlap_defect_le_deltaG_add_nonencoding
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (W : PauliKind)
    (hw : consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.place p1
        (((w.marginalPoly p1.side W).postprocess (fun g => MvPolynomial.eval u g.1)).effect a))
      (fun u a => S.place p2 ((S.pointMeasExp p2.side W u).effect a)) S.psiHat ≤ deltaG) :
    1 - avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
      ∑ g : Poly P, stateQForm S.psiHat
        (S.place p1 ((w.marginalPoly p1.side W).effect g) *
          S.place p2 ((S.pointMeasExp p2.side W u).effect
            (dotProduct (decodeFq g) (indicatorVec u))))) ≤
      deltaG + ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place p1 ((w.marginalPoly p1.side W).effect g)) := by
  rw [marginalPoly_pointMeasExp_consistencyDefect_eq] at hw
  have hcompare := avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _
    (fun u => marginal_eval_overlap_le_decoded_add_nonencoding w p1 p2 hopp W u)
  rw [avgOver_add, avgOver_const_of_isProbability _ (uniformDistribution_isProbability _)] at hcompare
  linarith

theorem tilde_m_consistent_point_meas_of_global_pair_witness_explicit :
    ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            consistencyDefect
              (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u a =>
                S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
              (fun u a => S.placeSide .bob
                (tildeM w .bob W (indicatorVec u) a))
              S.psiHat ≤
                deltaConstructPaulis (2 + 2 * Real.sqrt 172)
                  epsilon deltaG P.m P.d P.q := by
  classical
  intro P epsilon deltaG hepsilon _ hdeltaG S w W
  rw [tildeM_consistencyDefect_eq_one_sub_decoded_overlap]
  have hdefect := decoded_overlap_defect_le_deltaG_add_nonencoding w .BB' .AB'' trivial W
    (marginalPoly_pointMeas_consistent_bob w W)
  have href := (global_marginal_encoding_consistency_explicit P epsilon deltaG hepsilon S w W).2
  have hmass := (right_mass_outside_encoding_le_evaluated_defect
    (S.encodingPauliMeas .alice W) (w.marginalPoly .bob W)
    (ExtendedLineGame.pairState S) (ExtendedLineGame.pairState_norm S)
    (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .alice W)).trans
    (add_le_add href le_rfl)
  simp_rw [stateQForm_place_BB' S _
    (Matrix.nonneg_iff_posSemidef.mp ((w.marginalPoly .bob W).pos _)).isHermitian] at hdefect
  dsimp only [Placement.side] at hdefect
  unfold deltaConstructPaulis
  rw [Nat.cast_mul]
  have hratio : 0 ≤ (P.m * P.d : ℝ) / P.q := by positivity
  nlinarith [Real.sqrt_nonneg epsilon, Real.sqrt_nonneg (172 : ℝ)]

theorem tilde_m_consistent_point_meas'_of_global_pair_witness_explicit :
    ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            consistencyDefect
              (uniformDistribution (Fin P.m → PauliScalar P))
              (fun u a => S.placeSide .alice
                (tildeM w .alice W (indicatorVec u) a))
              (fun u a =>
                S.placePlayer .bob ((S.pointMeas .bob W u).effect a))
              S.psiHat ≤
                deltaConstructPaulis (2 + 2 * Real.sqrt 172)
                  epsilon deltaG P.m P.d P.q := by
  classical
  intro P epsilon deltaG hepsilon _ hdeltaG S w W
  rw [tildeM_consistencyDefect_eq_one_sub_decoded_overlap']
  have hdefect := decoded_overlap_defect_le_deltaG_add_nonencoding w .AA' .BA'' trivial W
    (marginalPoly_pointMeas_consistent_alice w W)
  have href := (global_marginal_encoding_consistency_explicit P epsilon deltaG hepsilon S w W).1
  have hmass := (mass_outside_encoding_le_evaluated_defect
    (w.marginalPoly .alice W) (S.encodingPauliMeas .bob W)
    (ExtendedLineGame.pairState S) (ExtendedLineGame.pairState_norm S)
    (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .bob W)).trans
    (add_le_add href le_rfl)
  simp_rw [stateQForm_place_AA' S _
    (Matrix.nonneg_iff_posSemidef.mp ((w.marginalPoly .alice W).pos _)).isHermitian] at hdefect
  dsimp only [Placement.side] at hdefect
  unfold deltaConstructPaulis
  rw [Nat.cast_mul]
  have hratio : 0 ≤ (P.m * P.d : ℝ) / P.q := by positivity
  nlinarith [Real.sqrt_nonneg epsilon, Real.sqrt_nonneg (172 : ℝ)]

end

end MIPStarRE.QPBT
