module

public import QPBT.Extraction.PointConsistency

/-!
# Point consistency with Alice's pulled-apart measurement

This module proves the register-interchanged overlap calculation for Item 1 of
blueprint `lem:qld-construct-the-paulis`. Polynomial evaluation is replaced by
decoded evaluation only on encoding outcomes; the remaining loss is bounded
by the mass of the non-encoding outcomes.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
* `docs/paper-gaps/qpbt_decoding-identity.tex` records the necessary restriction
  on the decoder identity.
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

/-- Placing a tensor with an identity on Alice's last register recovers `AA'`. -/
theorem placeSide_alice_tensor_one
    (B : Op (S.ExpandedLocalSpace .alice)) :
    S.placeSide .alice (heteroKron B (1 : Op (PauliRegister P))) = S.place .AA' B := by
  ext row col
  simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
    place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite]
  split_ifs <;> rfl

/-- The factors on `AA'A''` and `B` can be regrouped on `AA'` and `BA''`
without exchanging registers or assuming symmetry of the strategy. -/
theorem placeSide_alice_tensor_mul_placePlayer_bob
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

/-- Alice's extraction-block placement preserves finite sums. -/
theorem placeSide_alice_finset_sum
    {I : Type*} (s : Finset I) (B : I → Op (ExtractionBlock P S.toStrategy.ιA)) :
    S.placeSide .alice (∑ i ∈ s, B i) = ∑ i ∈ s, S.placeSide .alice (B i) := by
  classical
  change reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
    (heteroKron (∑ i ∈ s, B i) 1) = _
  rw [heteroKron_finset_sum_left]
  ext row col
  simp only [placeSide, reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.sum_apply]

end ProjectiveSetting

variable {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
  (w : GlobalPairWitness S deltaG) (W : PauliKind)

/-- The Alice-pulled/Bob-point overlap is exactly the expanded-point overlap
at the decoded value. This is the register-interchanged version of the first
three lines of the calculation in paper lines 1483--1492. -/
theorem sum_tildeM_mul_pointMeas_eq_decoded_overlap
    (u : PauliPoint P) :
    (∑ a : PauliScalar P, S.placeSide .alice (tildeM w .alice W (indicatorVec u) a) *
      S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) =
      ∑ g : Poly P, S.place .AA' ((w.marginalPoly .alice W).effect g) *
        S.place .BA'' ((S.pointMeasExp .bob W u).effect
          (dotProduct (decodeFq g) (indicatorVec u))) := by
  classical
  simp only [tildeM, S.placeSide_alice_finset_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1 with g
  simp only [S.placeSide_alice_tensor_mul_placePlayer_bob]
  rw [← Finset.mul_sum, ← S.place_finset_sum,
    S.pointMeasExp_effect_eq_sum_sub]

/-- The Alice-pulled/Bob-point consistency defect is one minus the decoded
overlap. This uses completeness but no encoding restriction or mass estimate. -/
theorem tildeM_consistencyDefect_eq_one_sub_decoded_overlap' :
    consistencyDefect (uniformDistribution (PauliPoint P))
      (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat =
      1 - avgOver (uniformDistribution (PauliPoint P)) (fun u =>
        ∑ g : Poly P, stateQForm S.psiHat
          (S.place .AA' ((w.marginalPoly .alice W).effect g) *
            S.place .BA'' ((S.pointMeasExp .bob W u).effect
              (dotProduct (decodeFq g) (indicatorVec u))))) := by
  classical
  let pulled : (PauliPoint P) → Measurement (PauliScalar P)
      (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := fun u =>
    Measurement.ofSumEqOne
      (fun a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
      (fun a => by
        apply ProjectiveSetting.reindexOp_nonneg
        exact kronecker_nonneg (tildeM_isProj w .alice W (indicatorVec u) a).nonneg
          Matrix.PosSemidef.one.nonneg)
      (by
        rw [← S.placeSide_alice_finset_sum, sum_tildeM_eq_one]
        change reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (heteroKron 1
            1) = 1
        rw [heteroKron_one_one]
        simp [reindexOp, Matrix.one_apply])
  have h := consistencyDefect_eq_one_sub_overlap pulled (fun u : Fin P.m → PauliScalar P =>
      S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u)))
    (uniformDistribution_isProbability _) S.psiHat_norm
  change _ = 1 - avgOver _ (fun u =>
    ∑ a : PauliScalar P, stateQForm S.psiHat
      (S.placeSide .alice (tildeM w .alice W (indicatorVec u) a) *
        S.placePlayer .bob ((S.pointMeas .bob W u).effect a))) at h
  apply h.trans
  congr 1
  apply avgOver_congr
  intro u
  simp [← stateQForm_finset_sum, sum_tildeM_mul_pointMeas_eq_decoded_overlap]

open scoped Classical in
/-- On Alice's marginal, replacing polynomial evaluation by decoded evaluation
loses at most the non-encoding mass. This is the support-restricted version of
the fourth line of paper lines 1483--1492, with the players interchanged. -/
theorem marginal_eval_overlap_le_decoded_add_nonencoding'
    (u : PauliPoint P) :
    (∑ g : Poly P, stateQForm S.psiHat
      (S.place .AA' ((w.marginalPoly .alice W).effect g) *
        S.place .BA'' ((S.pointMeasExp .bob W u).effect (MvPolynomial.eval u g.1)))) ≤
      (∑ g : Poly P, stateQForm S.psiHat
        (S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect
            (dotProduct (decodeFq g) (indicatorVec u))))) +
      ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g)) := by
  classical
  have hpos (g : Poly P) (a : PauliScalar P) :
      0 ≤ stateQForm S.psiHat
        _ :=
    stateQForm_nonneg _ (S.place_mul_place_nonneg .AA' .BA'' (by trivial)
      ((w.marginalPoly .alice W).pos g) ((S.pointMeasExp .bob W u).pos a))
  have hsum (g : Poly P) :
      (∑ a : PauliScalar P, stateQForm S.psiHat
        (S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect a))) =
        stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g)) := by
    have hc : (∑ a : PauliScalar P,
        S.place .BA'' _) = 1 :=
      (S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)).sum_eq_one
    simp [← stateQForm_finset_sum, ← Finset.mul_sum, hc]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  by_cases hg : IsEncoding g
  · simp_all
    rw [decodeFq_dotProduct_indicatorVec hg u]
    rfl
  · simp [*]
    have hle := Finset.single_le_sum (fun a _ => hpos g a)
      (Finset.mem_univ (MvPolynomial.eval u g.1))
    rw [hsum] at hle
    exact hle.trans (le_add_of_nonneg_left (hpos g _))



end

end MIPStarRE.QPBT
