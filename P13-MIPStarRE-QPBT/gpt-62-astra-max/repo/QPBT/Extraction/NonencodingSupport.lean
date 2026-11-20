module

public import QPBT.Extraction.EncodingSupport
public import QPBT.Extraction.PolynomialCollision
public import QPBT.Observables.IdealPointConsistency
public import QPBT.Games.SupportMass
public import QPBT.Games.DistanceTheorems.TensorConsistency
public import QPBT.Combining.Lines.PairStateConsistencyTransport
public import QPBT.Extraction.Observables

/-!
# Consistency with encoding-supported reference measurements

The Pauli-basis check remains a consistency estimate after adjoining the
perfectly correlated ideal point measurement. Schwartz-Zippel then controls
mass outside the encoding image by evaluated reference inconsistency.

## References

- Blueprint `eq:qld-nonencoding-mass` and `lem:qld-nonencoding-mass-bound`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:197-264,383-418`.
- `docs/paper-gaps/qpbt_decoding-identity.tex`.
- The reference measurements and comparison estimates express the convolution
  with the ideal Pauli point projectors.
- These are auxiliary estimates for a supplied witness, not its construction.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open scoped Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus ProjectiveSetting

noncomputable section

section

variable {P : AdmissibleParams} {X A I J : Type*} [Fintype X] [DecidableEq X] [Fintype A]
  [DecidableEq A] [Fintype I] [DecidableEq I]

/-- For commuting families, reversing the order of the measurements preserves
the consistency defect. This is finite-sum algebra for opposite placements. -/
theorem consistencyDefect_comm_of_commute (mu : Distribution X)
    (first second : X → A → Op I) (psi : EuclideanSpace ℂ I)
    (hcomm : ∀ x a b, first x a * second x b = second x b * first x a) :
    consistencyDefect mu first second psi = consistencyDefect mu second first psi := by
  simp [consistencyDefect]
  apply avgOver_congr
  intro x
  rw [Finset.sum_comm]
  congr 1 with b
  simp [hcomm, eq_comm]

/-- A polynomial measurement's mass outside the encoding image is at most
its evaluated inconsistency with an encoding-supported reference, plus `md/q`.
This is the Schwartz-Zippel step in blueprint `eq:qld-nonencoding-mass`.
The reference support is explicit because this auxiliary applies to any POVM;
the concrete reference above proves it without an additional strategy premise. -/
theorem mass_outside_encoding_le_evaluated_defect [Fintype J] [DecidableEq J]
    (meas : Measurement (Poly P) I) (reference : Measurement (Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1)
    (hsupport : ∀ g, ¬ IsEncoding g → reference.effect g = 0) :
    (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm psi (heteroKron (meas.effect g) 1)) ≤
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (fun u => meas.postprocess (fun g => evalPoly g u))
        (fun u => reference.postprocess
        (fun g => evalPoly g u)) psi + (P.m * P.d : ℝ) / P.q := by
  classical
  have hmass := mass_outside_support_le_point_defect meas reference psi
    (Finset.univ.filter IsEncoding) (by simpa using hsupport)
  simp at hmass
  refine hmass.trans ((SandwichProduct.point_codeword_defect_le_avg_evaluated_add
    meas reference psi evalPoly ((P.m * P.d) / P.q) hpsi
    (by positivity) poly_eval_collision_le).trans_eq ?_)
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point]

end

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ} (S : ProjectiveSetting P epsilon) (W : PauliKind)

/-- Adjoining the ideal point outcomes preserves the Pauli-basis check on the
two-player expanded state, in the point--Pauli orientation. -/
theorem point_encodingPauli_consistency_eq :
    bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeasExp .alice W)
        (fun u => (S.encodingPauliMeas .bob W).postprocess
        (fun g => evalPoly g u)) (ExtendedLineGame.pairState S) =
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeas .alice W)
        (S.pauliEvalMeas .bob W)
        S.toStrategy.ψ := by
  simp only [bipartiteDefect]
  simp_rw [encodingPauliMeas_eval_effect_eq_convolution S .bob W]
  simpa only [bipartiteDefect, pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution,
    tauPointMeas, ExtendedLineGame.pairState] using (consistencyDefect_convolution_eq_of_perfect
      (uniformDistribution (Fin P.m → PauliScalar P))
      (S.pointMeas .alice W) (S.pauliEvalMeas .bob W)
      (tauPointMeas W) (tauPointMeas W) S.toStrategy.ψ (eprState_norm _)
      (tauPointProj_epr_offDiagonal_eq_zero W))

/-- The same exact preservation holds in the Pauli--point orientation. -/
theorem encodingPauli_point_consistency_eq :
    bipartiteDefect (uniformDistribution (PauliPoint P))
        (fun u => (S.encodingPauliMeas .alice W).postprocess
        (fun g => evalPoly g u))
        (S.pointMeasExp .bob W)
        (ExtendedLineGame.pairState S) =
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pauliEvalMeas .alice W)
        (S.pointMeas .bob W)
        S.toStrategy.ψ := by
  simp only [bipartiteDefect]
  simp_rw [encodingPauliMeas_eval_effect_eq_convolution S .alice W]
  simpa only [bipartiteDefect, pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution,
    tauPointMeas, ExtendedLineGame.pairState] using (consistencyDefect_convolution_eq_of_perfect
      (uniformDistribution (Fin P.m → PauliScalar P))
      (S.pauliEvalMeas .alice W) (S.pointMeas .bob W)
      (tauPointMeas W) (tauPointMeas W) S.toStrategy.ψ (eprState_norm _)
      (tauPointProj_epr_offDiagonal_eq_zero W))

/-- Adjoining the same ideal point measurements also preserves point
self-consistency exactly. -/
theorem expanded_point_consistency_eq :
    bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeasExp .alice W)
        (S.pointMeasExp .bob W)
        (ExtendedLineGame.pairState S) =
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeas .alice W)
        (S.pointMeas .bob W)
        S.toStrategy.ψ := by
  simpa only [bipartiteDefect, pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution,
    tauPointMeas, ExtendedLineGame.pairState] using (consistencyDefect_convolution_eq_of_perfect
      _
      _ (S.pointMeas .bob W)
      (tauPointMeas W) (tauPointMeas W) S.toStrategy.ψ
      (φ := _) (eprState_norm _)
      (tauPointProj_epr_offDiagonal_eq_zero W))

end ProjectiveSetting

/-- For a supplied global polynomial-pair witness, both evaluated global
marginals are consistent with the opposite encoding-supported reference.
The universal square-root coefficient comes from the two Pauli-basis checks
and point self-consistency. This estimate neither assumes a separate
non-encoding support bound nor constructs the global witness. -/
theorem global_marginal_encoding_consistency_explicit :
    ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
      0 ≤ epsilon → ∀ (S : ProjectiveSetting P epsilon)
        (w : GlobalPairWitness S deltaG) (W : PauliKind),
      bipartiteDefect (uniformDistribution (PauliPoint P))
          (fun u => (w.marginalPoly .alice W).postprocess
          (fun g => evalPoly g u))
          (fun u => (S.encodingPauliMeas .bob W).postprocess
          (fun g => evalPoly g u)) (ExtendedLineGame.pairState S) ≤
        deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon ∧
      bipartiteDefect (uniformDistribution (PauliPoint P))
          (fun u => (S.encodingPauliMeas .alice W).postprocess
          (fun g => evalPoly g u))
          (fun u => (w.marginalPoly .bob W).postprocess
          (fun g => evalPoly g u)) (ExtendedLineGame.pairState S) ≤
        deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon := by
  intro P epsilon deltaG hepsilon S w W
  let mu := uniformDistribution (PauliPoint P)
  let psi := ExtendedLineGame.pairState S
  let pointA := fun u => leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    (S.pointMeasExp .alice W u)
  let pointB := fun u => rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    (S.pointMeasExp .bob W u)
  let refA := fun u => leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    ((S.encodingPauliMeas .alice W).postprocess (fun g => evalPoly g u))
  let refB := fun u => rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    ((S.encodingPauliMeas .bob W).postprocess (fun g => evalPoly g u))
  let margA := fun u => leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    ((w.marginalPoly .alice W).postprocess (fun g => evalPoly g u))
  let margB := fun u => rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    ((w.marginalPoly .bob W).postprocess (fun g => evalPoly g u))
  have hpost (side : PlayerSide) (u : PauliPoint P) :
      (w.marginalPoly side W).postprocess (fun g => evalPoly g u) =
        (w.Smeas side).postprocess (evalAt W u) := by
    rw [GlobalPairWitness.marginalPoly, Measurement.postprocess_comp]
    cases W <;> rfl
  have hpoints : consistencyDefect mu (fun u => (pointA u).effect)
      (fun u => (pointB u).effect) psi ≤ 86 * epsilon := by
    change bipartiteDefect mu
      _
      (S.pointMeasExp .bob W) psi ≤ _
    rw [S.expanded_point_consistency_eq]
    simpa only [pauli_edge_card, Nat.cast_ofNat] using point_self_consistency_le S W
  have hscalar : deltaG + 2 * Real.sqrt (86 * epsilon + 86 * epsilon) ≤
      deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon := by
    simp [← add_mul, show (86 : ℝ) + 86 = 172 by norm_num]
    nlinarith [Real.sqrt_nonneg epsilon]
  constructor
  · exact (consistencyDefect_trans_le mu margA pointB pointA refB psi
      deltaG _ _ (uniformDistribution_isProbability _)
      (ExtendedLineGame.pairState_norm S) (by
        change bipartiteDefect mu _
          (S.pointMeasExp .bob W) psi ≤ deltaG
        rw [S.consistencyDefect_pairState_eq_AA'_BA'']
        simpa only [hpost] using w.point_consistent_alice W) hpoints (by
        change bipartiteDefect mu (S.pointMeasExp .alice W)
          _ psi ≤ _
        rw [S.point_encodingPauli_consistency_eq]
        apply WinImplications.win_pauli_basis_cons_explicit <;> assumption)).trans hscalar
  · have h := (consistencyDefect_trans_le mu margB pointA pointB refA psi
      deltaG _ _ (uniformDistribution_isProbability _)
      (ExtendedLineGame.pairState_norm S) (by
        rw [consistencyDefect_comm_of_commute _ _ _ _ (by
          intro u a b
          exact (WinImplications.heteroKron_left_right_comm _ _).symm)]
        change bipartiteDefect mu (S.pointMeasExp .alice W)
          _ psi ≤ deltaG
        rw [S.consistencyDefect_pairState_eq_AB''_BB',
          consistencyDefect_comm_of_commute _ _ _ _ (by
            intro u a b
            solve_by_elim [S.place_comm])]
        simpa only [hpost] using w.point_consistent_bob W) (by
        rw [consistencyDefect_comm_of_commute _ _ _ _ (by
          intro u a b
          exact (WinImplications.heteroKron_left_right_comm _ _).symm)]
        exact hpoints) (by
        rw [consistencyDefect_comm_of_commute _ _ _ _ (by
          intro u a b
          exact (WinImplications.heteroKron_left_right_comm _ _).symm)]
        change bipartiteDefect mu _
          (S.pointMeasExp .bob W) psi ≤ _
        rw [S.encodingPauli_point_consistency_eq]
        apply WinImplications.win_pauli_basis_cons_interchanged_explicit <;> assumption)).trans hscalar
    rw [consistencyDefect_comm_of_commute _ _ _ _ (by
      intro u a b
      exact (WinImplications.heteroKron_left_right_comm _ _).symm)] at h
    exact h

variable {P : AdmissibleParams} {epsilon : ℝ} (S : ProjectiveSetting P epsilon)

/-- A marginal acting on `AA'` has the same mass in the extraction-block
notation and the two-player expanded state. The unused registers carry identities. -/
theorem stateQForm_placeSide_alice_tensor_one (A : Op (S.ExpandedLocalSpace .alice))
    (hA : A.IsHermitian) :
    stateQForm S.psiHat (S.placeSide .alice (heteroKron A (1 : Op (PauliRegister P)))) =
      stateQForm (ExtendedLineGame.pairState S) (heteroKron A 1) := by
  have hplace : S.placeSide .alice (heteroKron A 1) =
      S.place .AA' A := by
    ext row col
    simp only [placeSide, sixRegExtractionEquiv, reindexOp, place, heteroKron,
      Matrix.kronecker, Matrix.one_apply, mul_ite, ite_mul]
    split_ifs <;> simp_all
  rw [hplace]
  have h := ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S A 1 hA
    Matrix.isHermitian_one
  have hone : S.place .BA'' 1 = 1 := by
    solve_by_elim [S.place_one]
  simp_all

/-- The corresponding marginal-mass identity for `BB'`. The opposite placement
uses the second EPR pair, as in the witness's Bob consistency hypothesis. -/
theorem stateQForm_placeSide_bob_tensor_one (B : Op (S.ExpandedLocalSpace .bob))
    (hB : B.IsHermitian) :
    stateQForm S.psiHat (S.placeSide .bob (heteroKron B (1 : Op (PauliRegister P)))) =
      stateQForm (ExtendedLineGame.pairState S) (heteroKron 1 B) := by
  have hplace : S.placeSide .bob (heteroKron B 1) =
      S.place .BB' B := by
    ext row col
    simp only [placeSide, sixRegExtractionEquiv, reindexOp, place, heteroKron,
      Matrix.kronecker, Matrix.one_apply, mul_ite, ite_mul]
    split_ifs <;> simp_all
  rw [hplace]
  have h := ExtendedLineGame.stateQForm_pairState_eq_AB''_BB'
    Matrix.isHermitian_one hB
  have hone : S.place .AB'' 1 = 1 := by
    solve_by_elim [S.place_one]
  simp_all

end

end MIPStarRE.QPBT
