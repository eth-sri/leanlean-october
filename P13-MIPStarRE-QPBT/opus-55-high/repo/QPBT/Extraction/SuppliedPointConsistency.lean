module

public import QPBT.Extraction.Consistency
public import QPBT.Extraction.PointConsistencyPrime
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

variable {P : AdmissibleParams} {epsilon deltaG : ℝ}

open scoped Classical in
/-- A point-consistency bound for the evaluated marginal polynomial measurement
controls the decoded overlap up to the non-encoding mass. This is the
support-restricted calculation in paper
`14_analysis_of_the_pauli_basis_test.tex:1483-1492`. -/
theorem decoded_overlap_defect_le {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) (p q : Placement) (hpq : p.IsOpposite q)
    (hw : consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.place p (((w.marginalPoly p.side W).postprocess
          (fun g => MvPolynomial.eval u g.1)).effect a))
      (fun u a => S.place q ((S.pointMeasExp q.side W u).effect a)) S.psiHat ≤ deltaG) :
    1 - avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        ∑ g : Poly P, stateQForm S.psiHat
          (S.place p ((w.marginalPoly p.side W).effect g) *
            S.place q ((S.pointMeasExp q.side W u).effect
              (dotProduct (decodeFq g) (indicatorVec u))))) ≤
      deltaG + ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place p ((w.marginalPoly p.side W).effect g)) := by
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let M := w.marginalPoly p.side W
  replace hw := (consistencyDefect_eq_one_sub_overlap mu
    (fun u => S.placedMeasurement p (M.postprocess (fun g => MvPolynomial.eval u g.1)))
    (fun u => S.placedMeasurement q (S.pointMeasExp q.side W u)) S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm).symm.trans_le hw
  have hregroup (u : Fin P.m → PauliScalar P) :
      (∑ a : PauliScalar P, stateQForm S.psiHat
        (S.place p ((M.postprocess (fun g => MvPolynomial.eval u g.1)).effect a) *
          S.place q ((S.pointMeasExp q.side W u).effect a))) =
      ∑ g : Poly P, stateQForm S.psiHat
        (S.place p (M.effect g) * S.place q ((S.pointMeasExp q.side W u).effect
            (MvPolynomial.eval u g.1))) := by
    rw [← stateQForm_finset_sum, sum_marginalPoly_eval_mul w p W u, stateQForm_finset_sum]
  have hcompare (u : Fin P.m → PauliScalar P) :
      (∑ g : Poly P, stateQForm S.psiHat
        (S.place p (M.effect g) * S.place q ((S.pointMeasExp q.side W u).effect
          (MvPolynomial.eval u g.1)))) ≤
      (∑ g : Poly P, stateQForm S.psiHat
        (S.place p (M.effect g) * S.place q ((S.pointMeasExp q.side W u).effect
            (dotProduct (decodeFq g) (indicatorVec u))))) +
      ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place p (M.effect g)) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun g _ => ?_
    by_cases hg : IsEncoding g
    · simp only [hg, not_true_eq_false, ite_false, add_zero]
      rw [decodeFq_dotProduct_indicatorVec hg u]
      rfl
    · have hle := Finset.single_le_sum (fun a _ => stateQForm_nonneg S.psiHat
        (S.place_mul_place_nonneg p q hpq (M.pos g) ((S.pointMeasExp q.side W u).pos a)))
        (Finset.mem_univ (MvPolynomial.eval u g.1))
      rw [← stateQForm_finset_sum, ← Finset.mul_sum,
        ← ProjectiveSetting.place_finsetSum, (S.pointMeasExp q.side W u).sum_eq_one,
        ProjectiveSetting.place_one, mul_one] at hle
      simp only [hg, not_false_eq_true, ite_true]
      exact le_add_of_nonneg_of_le (stateQForm_nonneg S.psiHat (S.place_mul_place_nonneg p q hpq
        (M.pos g) ((S.pointMeasExp q.side W u).pos _))) hle
  have h := avgOver_mono mu _ _ hcompare
  rw [avgOver_add, avgOver_const_of_isProbability mu (uniformDistribution_isProbability _)] at h
  simp only [ProjectiveSetting.placedMeasurement_effect, hregroup] at hw
  linarith

/-- For a supplied global polynomial-pair witness, the pulled-apart defect is
bounded by its point-consistency error plus the non-encoding mass. This is the
support-restricted form of the calculation in paper
`14_analysis_of_the_pauli_basis_test.tex:1483-1492`, supporting blueprint
`lem:qld-construct-the-paulis`. It uses no estimate for the non-encoding mass;
the need for that separate estimate is explained in
`docs/paper-gaps/qpbt_decoding-identity.tex`. -/
theorem tildeM_consistencyDefect_le_deltaG_add_nonencoding
    {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat ≤
      deltaG + nonencodingMarginalMass w .bob W := by
  rw [tildeM_consistencyDefect_eq_one_sub_decoded_overlap]
  unfold nonencodingMarginalMass
  simp only [S.placeSide_bob_tensor_one]
  exact decoded_overlap_defect_le w W .BB' .AB'' trivial (marginalPoly_pointMeas_consistent_bob w W)

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
  have hdefect := tildeM_consistencyDefect_le_deltaG_add_nonencoding w W
  have href :=
    (global_marginal_encoding_consistency_explicit P epsilon deltaG hepsilon S w W).2
  have hmass := right_mass_outside_encoding_le_evaluated_defect
    (S.encodingPauliMeas .alice W) (w.marginalPoly .bob W)
    (ExtendedLineGame.pairState S) (ExtendedLineGame.pairState_norm S)
    (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .alice W)
  have hm : nonencodingMarginalMass w .bob W ≤
      deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon +
        (P.m * P.d : ℝ) / P.q := by
    unfold nonencodingMarginalMass
    change (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm S.psiHat (S.placeSide .bob
        (heteroKron ((w.marginalPoly .bob W).effect g) (1 : Op (PauliRegister P))))) ≤ _
    simp_rw [stateQForm_placeSide_bob_tensor_one S _
      (Matrix.nonneg_iff_posSemidef.mp ((w.marginalPoly .bob W).pos _)).isHermitian]
    exact hmass.trans (add_le_add href le_rfl)
  unfold deltaConstructPaulis
  rw [Nat.cast_mul]
  have hratio : 0 ≤ (P.m * P.d : ℝ) / P.q := by positivity
  have hsqrt := Real.sqrt_nonneg epsilon
  have hroot : 0 ≤ Real.sqrt (172 : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- For a supplied global polynomial-pair witness, the Alice-pulled/Bob-point
defect is bounded by its point-consistency error plus Alice's non-encoding
mass. This is the register-interchanged, support-restricted calculation in
paper `14_analysis_of_the_pauli_basis_test.tex:1483-1492`, supporting blueprint
`lem:qld-construct-the-paulis`. The estimate uses no bound for that mass; see
`docs/paper-gaps/qpbt_decoding-identity.tex` for the decoder restriction. -/
theorem tildeM_consistencyDefect_le_deltaG_add_nonencoding'
    {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤
      deltaG + nonencodingMarginalMass w .alice W := by
  rw [tildeM_consistencyDefect_eq_one_sub_decoded_overlap']
  unfold nonencodingMarginalMass
  simp only [S.placeSide_alice_tensor_one]
  exact decoded_overlap_defect_le w W .AA' .BA'' trivial (marginalPoly_pointMeas_consistent_alice w W)

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
  have hdefect := tildeM_consistencyDefect_le_deltaG_add_nonencoding' w W
  have href :=
    (global_marginal_encoding_consistency_explicit P epsilon deltaG hepsilon S w W).1
  have hmass := mass_outside_encoding_le_evaluated_defect
    (w.marginalPoly .alice W) (S.encodingPauliMeas .bob W)
    (ExtendedLineGame.pairState S) (ExtendedLineGame.pairState_norm S)
    (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .bob W)
  have hm : nonencodingMarginalMass w .alice W ≤
      deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon +
        (P.m * P.d : ℝ) / P.q := by
    unfold nonencodingMarginalMass
    change (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm S.psiHat (S.placeSide .alice
        (heteroKron ((w.marginalPoly .alice W).effect g) (1 : Op (PauliRegister P))))) ≤ _
    simp_rw [stateQForm_placeSide_alice_tensor_one S _
      (Matrix.nonneg_iff_posSemidef.mp ((w.marginalPoly .alice W).pos _)).isHermitian]
    exact hmass.trans (add_le_add href le_rfl)
  unfold deltaConstructPaulis
  rw [Nat.cast_mul]
  have hratio : 0 ≤ (P.m * P.d : ℝ) / P.q := by positivity
  have hsqrt := Real.sqrt_nonneg epsilon
  have hroot : 0 ≤ Real.sqrt (172 : ℝ) := Real.sqrt_nonneg _
  nlinarith

end

end MIPStarRE.QPBT
