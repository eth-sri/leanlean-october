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

/-- A polynomial measurement's mass outside the encoding image is at most
its evaluated inconsistency with an encoding-supported reference, plus `md/q`.
This is the Schwartz-Zippel step in blueprint `eq:qld-nonencoding-mass`.
The reference support is explicit because this auxiliary applies to any POVM;
the concrete reference above proves it without an additional strategy premise. -/
theorem mass_outside_encoding_le_evaluated_defect {P : AdmissibleParams}
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
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
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmass
  have hcollision := SandwichProduct.point_codeword_defect_le_avg_evaluated_add
    meas reference psi evalPoly ((P.m * P.d : ℝ) / P.q) hpsi
    (by positivity) poly_eval_collision_le
  refine hmass.trans (hcollision.trans_eq ?_)
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point]

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- Adjoin an ideal point answer and add it to the original answer. -/
private def pointConvolution {I : Type*} [Fintype I] [DecidableEq I]
    (W : PauliKind) (A : PauliPoint P → Measurement (PauliScalar P) I) :
    PauliPoint P → Measurement (PauliScalar P) (I × PauliRegister P) :=
  fun u => (tensorMeasurement (A u) (tauPointMeas W u)).postprocess (fun ab => ab.1 + ab.2)

section

variable (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind)
include S side W

private theorem pointMeasExp_eq_convolution :
    S.pointMeasExp side W = pointConvolution W (S.pointMeas side W) := by
  funext u
  apply Quantum.Measurement.ext
  intro c
  simp only [pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution,
    pointConvolution, Measurement.postprocess_effect, tensorMeasurement, tauPointMeas_effect]

private theorem encodingEval_eq_convolution :
    (fun u => (S.encodingPauliMeas side W).postprocess (fun g => evalPoly g u)) =
      pointConvolution W (S.pauliEvalMeas side W) := by
  funext u
  apply Quantum.Measurement.ext
  intro c
  rw [encodingPauliMeas_eval_effect_eq_convolution]
  rfl

end

/-- A common perfectly correlated ideal point shift preserves the defect. -/
private theorem pointConvolution_defect (S : ProjectiveSetting P ε) (W : PauliKind)
    (A : PauliPoint P → Measurement (PauliScalar P) S.toStrategy.ιA)
    (B : PauliPoint P → Measurement (PauliScalar P) S.toStrategy.ιB) :
    bipartiteDefect (uniformDistribution _) (pointConvolution W A) (pointConvolution W B)
      (ExtendedLineGame.pairState S) = bipartiteDefect (uniformDistribution _) A B S.toStrategy.ψ :=
  bipartiteDefect_tensor_shift_eq _ A B (tauPointMeas W) (tauPointMeas W) _
    (eprState (PauliRegister P)) (eprState_norm _)
    (fun a c => a + c) (fun _ _ _ => add_right_cancel)
    (fun u _ _ => tauPointProj_epr_joint_eq_zero_of_ne W u)
    (sum_tauPointProj_pair_stateQForm_eprState W)

end ProjectiveSetting

/-- The right-hand marginal version of the support estimate, obtained by
interchanging the two tensor factors and using the same collision bound. -/
theorem right_mass_outside_encoding_le_evaluated_defect {P : AdmissibleParams}
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (reference : Measurement (Poly P) I) (meas : Measurement (Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1)
    (hsupport : ∀ g, ¬ IsEncoding g → reference.effect g = 0) :
    (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm psi (heteroKron 1 (meas.effect g))) ≤
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (fun u => reference.postprocess
          (fun g => evalPoly g u))
        (fun u => meas.postprocess (fun g => evalPoly g u))
        psi + (P.m * P.d : ℝ) / P.q := by
  have h := mass_outside_encoding_le_evaluated_defect meas reference
    (reindexState (Equiv.prodComm I J) psi)
    (by rw [reindexState_norm_eq, hpsi]) hsupport
  simpa only [DistanceCalculus.stateQForm_reindexState,
    reindexOp_prodComm_heteroKron,
    DistanceCalculus.consistencyDefect_prodComm] using h

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
  let left := leftPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    (ιB := S.ExpandedLocalSpace .bob) (α := PauliScalar P)
  let right := rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    (ιB := S.ExpandedLocalSpace .bob) (α := PauliScalar P)
  let pointA := fun u => left
    (S.pointMeasExp .alice W u)
  let pointB := fun u => right
    (S.pointMeasExp .bob W u)
  let refA := fun u => left
    ((S.encodingPauliMeas .alice W).postprocess (fun g => evalPoly g u))
  let refB := fun u => right
    ((S.encodingPauliMeas .bob W).postprocess (fun g => evalPoly g u))
  let margA := fun u => left
    ((w.marginalPoly .alice W).postprocess (fun g => evalPoly g u))
  let margB := fun u => right
    ((w.marginalPoly .bob W).postprocess (fun g => evalPoly g u))
  have hab : measurementDefect mu margA
      pointB psi ≤ deltaG := by
    change bipartiteDefect mu
      (fun u => (w.marginalPoly .alice W).postprocess
        (fun g => evalPoly g u))
      (S.pointMeasExp .bob W) psi ≤ deltaG
    rw [S.consistencyDefect_pairState_eq_AA'_BA'']
    simpa only [w.marginalPoly_postprocess_eval] using w.point_consistent .alice W
  have hba : measurementDefect mu margB pointA psi ≤ deltaG := by
    rw [measurementDefect_symm]
    change bipartiteDefect mu (S.pointMeasExp .alice W)
      (fun u => (w.marginalPoly .bob W).postprocess (fun g => evalPoly g u)) psi ≤ deltaG
    rw [S.consistencyDefect_pairState_eq_BB'_AB'']
    simpa only [w.marginalPoly_postprocess_eval] using w.point_consistent .bob W
  have hpoints : measurementDefect mu pointA
      pointB psi ≤ 86 * epsilon := by
    change bipartiteDefect mu
      (S.pointMeasExp .alice W)
      (S.pointMeasExp .bob W) psi ≤ _
    rw [pointMeasExp_eq_convolution, pointMeasExp_eq_convolution, pointConvolution_defect]
    simpa only [pauli_edge_card, Nat.cast_ofNat] using point_self_consistency_le S W
  have hpoints' : measurementDefect mu pointB pointA psi ≤ 86 * epsilon :=
    (measurementDefect_symm mu pointB pointA psi).trans_le hpoints
  have hpb : measurementDefect mu pointA
      refB psi ≤ 86 * epsilon := by
    change bipartiteDefect mu
      (S.pointMeasExp .alice W)
      (fun u => (S.encodingPauliMeas .bob W).postprocess
        (fun g => evalPoly g u)) psi ≤ _
    rw [pointMeasExp_eq_convolution, encodingEval_eq_convolution, pointConvolution_defect]
    exact WinImplications.win_pauli_basis_cons_explicit P epsilon S hepsilon W
  have hpa : measurementDefect mu pointB
      refA psi ≤ 86 * epsilon := by
    rw [measurementDefect_symm]
    change bipartiteDefect mu
      (fun u => (S.encodingPauliMeas .alice W).postprocess
        (fun g => evalPoly g u))
      (S.pointMeasExp .bob W) psi ≤ _
    rw [encodingEval_eq_convolution, pointMeasExp_eq_convolution, pointConvolution_defect]
    exact WinImplications.win_pauli_basis_cons_interchanged_explicit
      P epsilon S hepsilon W
  have hscalar : deltaG + 2 * Real.sqrt (86 * epsilon + 86 * epsilon) ≤
      deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon := by
    rw [← add_mul, show (86 : ℝ) + 86 = 172 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 172)]
    nlinarith [Real.sqrt_nonneg epsilon]
  constructor
  · exact (consistencyDefect_trans_le mu margA pointB pointA refB psi
      deltaG (86 * epsilon) (86 * epsilon) (uniformDistribution_isProbability _)
      (ExtendedLineGame.pairState_norm S) hab hpoints hpb).trans hscalar
  · have h := (consistencyDefect_trans_le mu margB pointA pointB refA psi
      deltaG (86 * epsilon) (86 * epsilon) (uniformDistribution_isProbability _)
      (ExtendedLineGame.pairState_norm S) hba hpoints' hpa).trans hscalar
    rw [measurementDefect_symm] at h
    exact h

section

variable {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon)
include P epsilon S

/-- A marginal acting on `AA'` has the same mass in the extraction-block
notation and the two-player expanded state. The unused registers carry identities. -/
theorem stateQForm_placeSide_alice_tensor_one (A : Op (S.ExpandedLocalSpace .alice))
    :
    stateQForm S.psiHat (S.placeSide .alice (heteroKron A (1 : Op (PauliRegister P)))) =
      stateQForm (ExtendedLineGame.pairState S) (heteroKron A 1) := by
  rw [S.placeSide_alice_tensor_one]
  simpa only [ProjectiveSetting.placedCorrelation, S.place_one, Matrix.mul_one] using
    (ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S A 1).symm

/-- The corresponding marginal-mass identity for `BB'`. The opposite placement
uses the second EPR pair, as in the witness's Bob consistency hypothesis. -/
theorem stateQForm_placeSide_bob_tensor_one (B : Op (S.ExpandedLocalSpace .bob))
    :
    stateQForm S.psiHat (S.placeSide .bob (heteroKron B (1 : Op (PauliRegister P)))) =
      stateQForm (ExtendedLineGame.pairState S) (heteroKron 1 B) := by
  rw [S.placeSide_bob_tensor_one]
  simpa only [ProjectiveSetting.placedCorrelation, S.place_one, Matrix.one_mul] using
    (ExtendedLineGame.stateQForm_pairState_eq_AB''_BB' S 1 B).symm

end

end

end MIPStarRE.QPBT
