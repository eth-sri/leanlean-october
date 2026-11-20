module

public import QPBT.Extraction.Consistency
public import QPBT.Extraction.PointConsistencyPrime

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

/-- For a supplied global polynomial-pair witness, the pulled-apart defect is
bounded by its point-consistency error plus the non-encoding mass. This is the
support-restricted form of the calculation in paper
`14_analysis_of_the_pauli_basis_test.tex:1483-1492`, supporting blueprint
`lem:qld-construct-the-paulis`. It uses no estimate for the non-encoding mass;
the need for that separate estimate is explained in
`docs/paper-gaps/qpbt_decoding-identity.tex`. -/
theorem tildeM_consistencyDefect_le_deltaG_add_nonencoding
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (PauliPoint P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat ≤
      deltaG + nonencodingMarginalMass w .bob W := by
  classical
  let mu := uniformDistribution (PauliPoint P)
  let evaluated := fun u : PauliPoint P =>
    S.placedMeasurement .BB' ((w.marginalPoly .bob W).postprocess
      (fun g => MvPolynomial.eval u g.1))
  let expanded := fun u : PauliPoint P =>
    S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)
  have hw := marginalPoly_pointMeas_consistent_bob w W
  change consistencyDefect mu (fun u => (evaluated u).effect)
    (fun u => (expanded u).effect) S.psiHat ≤ deltaG at hw
  rw [(consistencyDefect_eq_one_sub_overlap evaluated expanded
    (uniformDistribution_isProbability _) S.psiHat_norm)] at hw
  have hregroup (u : PauliPoint P) :
      (∑ a : PauliScalar P, stateQForm S.psiHat
        ((evaluated u).effect a * (expanded u).effect a)) =
      ∑ g : Poly P, stateQForm S.psiHat
        (S.place .BB' ((w.marginalPoly .bob W).effect g) *
          S.place .AB'' ((S.pointMeasExp .alice W u).effect
            (MvPolynomial.eval u g.1))) := by
    rw [← stateQForm_finset_sum]
    exact (congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .BB' W u
        _)).trans
      (stateQForm_finset_sum _ _ _)
  simp only [hregroup] at hw
  have hcompare := avgOver_mono mu _ _
    (marginal_eval_overlap_le_decoded_add_nonencoding w W)
  rw [avgOver_add, avgOver_const_of_isProbability mu
    (uniformDistribution_isProbability _)] at hcompare
  have hmass_eq : nonencodingMarginalMass w .bob W =
      ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place .BB' ((w.marginalPoly .bob W).effect g)) := by
    unfold nonencodingMarginalMass
    simp only [S.placeSide_bob_tensor_one]
    rfl
  rw [tildeM_consistencyDefect_eq_one_sub_decoded_overlap]
  linarith

/-- Conditional consistency of Alice's original point measurement with Bob's
pulled-apart measurement, averaged over uniformly random points. This is the
supplied-witness form of the first display of Item 1 in paper
`14_analysis_of_the_pauli_basis_test.tex:1463-1492`.

The source reuses `deltaS` after absorbing the non-encoding and game-error
terms. The bound keeps the global polynomial-pair witness error `deltaG`
separate in `deltaConstructPaulis`.

The encoding-supported reference and Schwartz--Zippel estimates in
`NonencodingSupport` control the non-encoding mass required by the restricted
decoder identity; see `docs/paper-gaps/qpbt_decoding-identity.tex`.
**Conditional:** The premise `w : GlobalPairWitness S deltaG` is supplied rather
than constructed here, so this declaration is not the source-facing result.
The theorem `exists_pulled_apart_consistency` now obtains the witness from
`exists_globalPairWitness`, including at zero error, and applies this estimate
together with the other two supplied-witness estimates to the same witness.
The completed composition and the remaining extraction obligations are recorded
in `docs/paper-gaps/qpbt_extraction-transfer.tex` under issue Dengnifer/MIPStarRE-QPBT-bak#123. -/
theorem tilde_m_consistent_point_meas_of_global_pair_witness_explicit :
    ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            consistencyDefect
              (uniformDistribution (PauliPoint P))
              (fun u a =>
                S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
              (fun u a => S.placeSide .bob
                (tildeM w .bob W (indicatorVec u) a))
              S.psiHat ≤
                deltaConstructPaulis (2 + 2 * Real.sqrt 172)
                  epsilon deltaG P.m P.d P.q := by
  classical
  intro P epsilon deltaG hepsilon _ hdeltaG S w W
  have hdefect := tildeM_consistencyDefect_le_deltaG_add_nonencoding w W
  have href :=
    (global_marginal_encoding_consistency_explicit P epsilon deltaG hepsilon S w W).2
  have hmass := by
                  simpa only [WinImplications.stateQForm_reindexState,
                    WinImplications.reindexOp_prodComm_heteroKron,
                    consistencyDefect_prodComm] using (mass_outside_encoding_le_evaluated_defect (w.marginalPoly .bob W) _
                      (reindexState (Equiv.prodComm _ _) _)
                      (by rw [reindexState_norm_eq, (ExtendedLineGame.pairState_norm S)]) (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .alice W))
  have hm : nonencodingMarginalMass w .bob W ≤
      deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon +
        (P.m * P.d) / P.q := by
    change (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm S.psiHat (S.placeSide .bob
        (heteroKron ((w.marginalPoly .bob W).effect g) 1))) ≤ _
    simp_rw [stateQForm_placeSide_bob_tensor_one S _
      (measurement_effect_hermitian (w.marginalPoly .bob W) _)]
    exact hmass.trans (add_le_add href le_rfl)
  unfold deltaConstructPaulis
  simp
  have hratio : 0 ≤ (P.m * P.d : ℝ) / P.q := by positivity
  have hsqrt := Real.sqrt_nonneg epsilon
  have hroot : 0 ≤ Real.sqrt 172 := Real.sqrt_nonneg _
  nlinarith

/-- For a supplied global polynomial-pair witness, the Alice-pulled/Bob-point
defect is bounded by its point-consistency error plus Alice's non-encoding
mass. This is the register-interchanged, support-restricted calculation in
paper `14_analysis_of_the_pauli_basis_test.tex:1483-1492`, supporting blueprint
`lem:qld-construct-the-paulis`. The estimate uses no bound for that mass; see
`docs/paper-gaps/qpbt_decoding-identity.tex` for the decoder restriction. -/
theorem tildeM_consistencyDefect_le_deltaG_add_nonencoding'
    {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (PauliPoint P))
      (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤
      deltaG + nonencodingMarginalMass w .alice W := by
  classical
  let mu := uniformDistribution (PauliPoint P)
  let evaluated := fun u : PauliPoint P =>
    S.placedMeasurement .AA' ((w.marginalPoly .alice W).postprocess
      (fun g => MvPolynomial.eval u g.1))
  let expanded := fun u : PauliPoint P =>
    S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)
  have hw := marginalPoly_pointMeas_consistent_alice w W
  change consistencyDefect mu (fun u => (evaluated u).effect)
    (fun u => (expanded u).effect) S.psiHat ≤ deltaG at hw
  rw [(consistencyDefect_eq_one_sub_overlap evaluated expanded
    (uniformDistribution_isProbability _) S.psiHat_norm)] at hw
  have hregroup (u : PauliPoint P) :
      (∑ a : PauliScalar P, stateQForm S.psiHat
        ((evaluated u).effect a * (expanded u).effect a)) =
      ∑ g : Poly P, stateQForm S.psiHat
        (S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect
            (MvPolynomial.eval u g.1))) := by
    rw [← stateQForm_finset_sum]
    exact (congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .AA' W u
        _)).trans
      (stateQForm_finset_sum _ _ _)
  simp only [hregroup] at hw
  have hcompare := avgOver_mono mu _ _
    (marginal_eval_overlap_le_decoded_add_nonencoding' w W)
  rw [avgOver_add, avgOver_const_of_isProbability mu
    (uniformDistribution_isProbability _)] at hcompare
  have hmass_eq : nonencodingMarginalMass w .alice W =
      ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g)) := by
    unfold nonencodingMarginalMass
    simp only [S.placeSide_alice_tensor_one]
    rfl
  rw [tildeM_consistencyDefect_eq_one_sub_decoded_overlap']
  linarith

/-- Conditional consistency of Alice's pulled-apart measurement with Bob's
original point measurement, averaged over uniformly random points. This is the
supplied-witness form of the register-interchanged display of Item 1 in paper
`14_analysis_of_the_pauli_basis_test.tex:1463-1492`.

The conclusion uses the same explicit construction scale as the first player
ordering.

The non-encoding mass is controlled by the encoding-supported reference and
Schwartz--Zippel estimates of `NonencodingSupport`. Thus the restricted decoder
identity suffices, as explained in `docs/paper-gaps/qpbt_decoding-identity.tex`.

**Conditional:** The premise `w : GlobalPairWitness S deltaG` is supplied rather
than constructed here, so this declaration is not the source-facing result.
The theorem `exists_pulled_apart_consistency` now obtains the witness from
`exists_globalPairWitness`, including at zero error, and applies this estimate
together with the other two supplied-witness estimates to the same witness.
The completed composition and the remaining extraction obligations are recorded
in `docs/paper-gaps/qpbt_extraction-transfer.tex` under issue Dengnifer/MIPStarRE-QPBT-bak#123. -/
theorem tilde_m_consistent_point_meas'_of_global_pair_witness_explicit :
    ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG) (W : PauliKind),
            consistencyDefect
              (uniformDistribution (PauliPoint P))
              (fun u a => S.placeSide .alice
                (tildeM w .alice W (indicatorVec u) a))
              (fun u a =>
                S.placePlayer .bob ((S.pointMeas .bob W u).effect a))
              S.psiHat ≤
                deltaConstructPaulis (2 + 2 * Real.sqrt 172)
                  epsilon deltaG P.m P.d P.q := by
  classical
  intro P epsilon deltaG hepsilon _ hdeltaG S w W
  have hdefect := tildeM_consistencyDefect_le_deltaG_add_nonencoding' w W
  have href :=
    (global_marginal_encoding_consistency_explicit P epsilon deltaG hepsilon S w W).1
  have hmass := mass_outside_encoding_le_evaluated_defect
    (w.marginalPoly .alice W) _
    _ (ExtendedLineGame.pairState_norm S)
    (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .bob W)
  have hm : nonencodingMarginalMass w .alice W ≤
      deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon +
        (P.m * P.d) / P.q := by
    change (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm S.psiHat (S.placeSide .alice
        (heteroKron ((w.marginalPoly .alice W).effect g) 1))) ≤ _
    simp_rw [stateQForm_placeSide_alice_tensor_one S _
      (measurement_effect_hermitian (w.marginalPoly .alice W) _)]
    exact hmass.trans (add_le_add href le_rfl)
  unfold deltaConstructPaulis
  simp
  have hratio : 0 ≤ (P.m * P.d : ℝ) / P.q := by positivity
  have hsqrt := Real.sqrt_nonneg epsilon
  have hroot : 0 ≤ Real.sqrt 172 := Real.sqrt_nonneg _
  nlinarith

end

end MIPStarRE.QPBT
