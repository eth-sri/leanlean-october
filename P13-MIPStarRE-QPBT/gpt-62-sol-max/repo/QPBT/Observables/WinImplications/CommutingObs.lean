module

public import QPBT.Observables.WinImplications.PointObs

/-!
# Approximate commutation of the point observables on commuting tuples

This module carries out the commuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`: the chain of
consistency relations `eq:lc-11`, the commutation analysis
`lem:commutation-analysis`, and the expansion `eq:lc-12` of the observables in
terms of the trace-coarse-grained point projections.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-341`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Algebraic preliminaries -/

/-- The commutator of two reflections written as `1 - 2P` is four times the
commutator of the projections. This is the algebra of Equation `eq:lc-12`,
paper `14_analysis_of_the_pauli_basis_test.tex:330-341`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem reflection_commutator_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Op ι) :
    (1 - (2 : ℂ) • A) * (1 - (2 : ℂ) • B) -
        (1 - (2 : ℂ) • B) * (1 - (2 : ℂ) • A) =
      (4 : ℂ) • (A * B - B * A) := by
  have h2 : ∀ M : Op ι, (2 : ℂ) • M = M + M := fun M => two_smul ℂ M
  have h4 : ∀ M : Op ι, (4 : ℂ) • M = M + M + (M + M) := by
    intro M
    rw [show (4 : ℂ) = 2 + 2 by norm_num, add_smul, h2]
  rw [h2, h2, h4]
  noncomm_ring

/-- The strategy point observable is the reflection about the trace-coarse
grained point projection at label one. This is the first display of
Equation `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-336`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pointObs_eq_one_sub_two_smul {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : PauliPoint P) :
    S.pointObs side W r u =
      1 - (2 : ℂ) • (S.pointTraceMeas side W u r).effect 1 := by
  classical
  rw [pointObs_eq_traceMeas_obs, sum_zmod_two]
  have hsum : (S.pointTraceMeas side W u r).effect 0 +
      (S.pointTraceMeas side W u r).effect 1 = 1 := by
    have := (S.pointTraceMeas side W u r).sum_eq_one
    rwa [sum_zmod_two] at this
  have hzero : phaseSign (0 : ZMod 2) = 1 := by simp [phaseSign]
  have hone : phaseSign (1 : ZMod 2) = -1 := by
    have : (1 : ZMod 2) ≠ 0 := by decide
    simp [phaseSign, this]
  rw [hzero, hone, one_smul, neg_one_smul]
  have heff0 : (S.pointTraceMeas side W u r).effect 0 =
      1 - (S.pointTraceMeas side W u r).effect 1 := by
    rw [← hsum]; abel
  rw [heff0, two_smul]
  abel

/-! ## Pair/W self-consistency on commuting tuples -/

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind)
include P ε S W

/-- Pair/W self-consistency is the Pair/W self-loop label mismatch. This is
item 1 of `lem:qld-win-implications` read on the Pair/W questions, paper
`14_analysis_of_the_pauli_basis_test.tex:197-199,315-320`, blueprint
`ch14_qpbt_observables.tex:633-637`. -/
theorem pairWConsistency_eq_mismatch :
    bipartiteDefect (commTupleDist P)
        (S.pairWAt .alice W)
        (S.pairWAt .bob W)
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            ProjectiveSetting.pairWAnswerOrZero B)) := by
  let q (ω : PauliTuple P) :=
    ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  exact consistencyDefect_postprocess_eq_mismatch _ S.toStrategy q q
    (fun _ => ProjectiveSetting.pairWAnswerOrZero) (fun _ => ProjectiveSetting.pairWAnswerOrZero)

/-- The Pair/W measurements are self-consistent on commuting tuples. This is
item 1 of `lem:qld-win-implications` on the Pair/W questions, used in the
chain leading to Equation `eq:lc-11`, paper
`14_analysis_of_the_pauli_basis_test.tex:315-320`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pairW_self_consistency_comm_le :
    bipartiteDefect (commTupleDist P)
        (S.pairWAt .alice W)
        (S.pairWAt .bob W)
        S.toStrategy.ψ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  classical
  rw [pairWConsistency_eq_mismatch]
  calc
    _ ≤ 2 * avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        if IsCommuting ω then
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
            (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
              ProjectiveSetting.pairWAnswerOrZero B)
        else 0) := by
      apply avgOver_comm_le_two_mul_gated
      intro ω
      exact outcome_event_weight_nonneg S.toStrategy _ _ _
    _ ≤ 2 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (pauliLoopEdge (.pairW W))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← avgOver_pauliTuple_uniform]
      apply avgOver_mono
      intro z
      have hs : outcomeEventWeight S.toStrategy
          ((.pairW W), pauliCL P (.pairW W) z)
          ((.pairW W), pauliCL P (.pairW W) z)
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            ProjectiveSetting.pairWAnswerOrZero B) ≤
          pauliRejectionAt S.toStrategy (pauliLoopEdge (.pairW W)) z := by
        refine le_trans ?_ (loopMismatch_le_rejection S (.pairW W) z)
        apply outcome_event_weight_mono
        intro A B hne hAB
        exact hne (by rw [hAB])
      rw [pauliCL_shared_eq P (.pairW W) rfl] at hs
      by_cases hcomm : IsCommuting (pauliSharedSplit P z).1
      · simp only [if_pos hcomm]
        simpa [pauliSharedSplit_apply, ProjectiveSetting.pairWQuestion] using hs
      · simp only [if_neg hcomm]
        exact pauliRejectionAt_nonneg S.toStrategy _ z
    _ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _)
        (by norm_num)

end

/-! ## The chained relation of Equation `eq:lc-11` -/

/-- Chaining the commuting-case consistency relations gives the point/Pair
relation `eq:lc-11`. The statement is generic in the two tensor factors and in
the state, so that both orientations of `eq:pts-obs-commutation` use it. Paper
`14_analysis_of_the_pauli_basis_test.tex:311-322`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pointTrace_pairComponent_dist_le {P : AdmissibleParams}
    {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (MP QL : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
    (QR RR : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιR)
    (χ : EuclideanSpace ℂ (ιL × ιR)) (hχ : ‖χ‖ = 1) {c₁ c₂ c₃ : ℝ}
    (h1 : bipartiteDefect (commTupleDist P)
      MP
      QR χ ≤ c₁)
    (h2 : bipartiteDefect (commTupleDist P)
      QL
      QR χ ≤ c₂)
    (h3 : bipartiteDefect (commTupleDist P)
      QL
      RR χ ≤ c₃) :
    opFamilyDistSq (commTupleDist P)
      (fun ω a => heteroKron ((MP ω).effect a) 1)
      (fun ω a => heteroKron 1 ((RR ω).effect a)) χ ≤
        2 * (c₁ + 2 * Real.sqrt (c₂ + c₃)) := by
  classical
  have hchain := consistencyDefect_trans_le (commTupleDist P)
    (fun ω => DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (MP ω))
    (fun ω => DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (QR ω))
    (fun ω => DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (QL ω))
    (fun ω => DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (RR ω))
    χ c₁ c₂ c₃ (commTupleDist_isProbability P) hχ h1 h2 h3
  exact opFamilyDistSq_placed_le_of_consistencyDefect_le (commTupleDist P)
    MP RR χ hchain

/-! ## From projections to observables -/

/-- Writing the two observables as the reflections `1 - 2P` makes their
commutator four times the commutator of the two projections, so the squared
state-dependent norm of the observable commutator is sixteen times that of the
projection commutator, on every state and both tensor factors. This is the
passage from Equation `eq:qld-obs-comm` to the observables in Equation
`eq:lc-12`, paper `14_analysis_of_the_pauli_basis_test.tex:330-341`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem norm_pointObs_commutator_sq {ιL ιR : Type*} [Fintype ιL]
    [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR] (PX PZ OX OZ : Op ιL)
    (hX : OX = 1 - (2 : ℂ) • PX) (hZ : OZ = 1 - (2 : ℂ) • PZ)
    (χ : EuclideanSpace ℂ (ιL × ιR)) :
    ‖applyOperatorToState
        (heteroKron (OX * OZ) (1 : Op ιR) -
          heteroKron (OZ * OX) (1 : Op ιR)) χ‖ ^ 2 =
      16 * ‖applyOperatorToState
        (heteroKron (PX * PZ - PZ * PX) (1 : Op ιR)) χ‖ ^ 2 := by
  rw [← heteroKron_sub_left, hX, hZ, reflection_commutator_eq,
    heteroKron_smul_left, applyOperatorToState_smul_op, norm_smul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  ring

/-- The point observables approximately commute on commuting tuples. This is
the commuting half of Equation `eq:pts-obs-commutation`, stated generically in
the two tensor factors and the state.

The error has the form `c₁ + √(c₂ + c₃)` because the chain of Equation
`eq:lc-11` is closed by the transitivity estimate for the consistency relation
`≃`, which is not additive. Composing a consistency relation with a detour
through a third family passes through a squared state-dependent distance and a
Cauchy--Schwarz step, so the two defects `c₂` and `c₃` of the detour appear
under a square root, while the defect `c₁` of the step used directly enters
linearly. Paper
`14_analysis_of_the_pauli_basis_test.tex:311-341`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem point_obs_commutator_comm_le_explicit :
    ∀ {P : AdmissibleParams} {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL]
        [Fintype ιR] [DecidableEq ιR]
        (MX MZ QX QZ : PauliTuple P →
          MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
        (VX VZ : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιR)
        (N : PauliTuple P →
          MIPStarRE.Quantum.Measurement (ZMod 2 × ZMod 2) ιR)
        (OX OZ : PauliTuple P → Op ιL)
        (χ : EuclideanSpace ℂ (ιL × ιR)) {c₁ c₂ c₃ : ℝ},
      ‖χ‖ = 1 → 0 ≤ c₁ →
      (∀ ω, MIPStarRE.QPBT.Measurement.IsProjective (N ω)) →
      (∀ ω, OX ω = 1 - (2 : ℂ) • (MX ω).effect 1) →
      (∀ ω, OZ ω = 1 - (2 : ℂ) • (MZ ω).effect 1) →
      bipartiteDefect (commTupleDist P)
        MX
        VX χ ≤ c₁ →
      bipartiteDefect (commTupleDist P)
        MZ
        VZ χ ≤ c₁ →
      bipartiteDefect (commTupleDist P)
        QX
        VX χ ≤ c₂ →
      bipartiteDefect (commTupleDist P)
        QZ
        VZ χ ≤ c₂ →
      bipartiteDefect (commTupleDist P)
        QX
        (fun ω => (N ω).postprocess (fun bits => bits.1)) χ ≤ c₃ →
      bipartiteDefect (commTupleDist P)
        QZ
        (fun ω => (N ω).postprocess (fun bits => bits.2)) χ ≤ c₃ →
      avgOver (commTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
            heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2) ≤
        1024 * (c₁ + Real.sqrt (c₂ + c₃)) := by
  classical
  intro P ιL ιR _ _ _ _ MX MZ QX QZ VX VZ N OX OZ χ c₁ c₂ c₃ hn hc hp hx hz a1 a2 b1 b2 d1 d2
  set δ : ℝ := 2 * (c₁ + 2 * Real.sqrt (c₂ + c₃)) with hδdef
  have hchainX := pointTrace_pairComponent_dist_le MX QX VX
    (fun ω => (N ω).postprocess (fun bits => bits.1)) χ hn a1 b1 d1
  have hchainZ := pointTrace_pairComponent_dist_le MZ QZ VZ
    (fun ω => (N ω).postprocess (fun bits => bits.2)) χ hn a2 b2 d2
  have hproj := op_dist_sq_commutator_le_explicit (commTupleDist P) MX MZ N χ 1 1 hp hchainX hchainZ
  have hcongr : avgOver (commTupleDist P) (fun ω =>
      ‖applyOperatorToState
        (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
          heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2) =
    16 * avgOver (commTupleDist P) (fun ω =>
      ‖applyOperatorToState (heteroKron
        ((MX ω).effect 1 * (MZ ω).effect 1 -
          (MZ ω).effect 1 * (MX ω).effect 1) (1 : Op ιR)) χ‖ ^ 2) := by
    rw [← avgOver_const_mul]
    refine avgOver_congr _ _ _ (fun ω => ?_)
    exact norm_pointObs_commutator_sq ((MX ω).effect 1) ((MZ ω).effect 1)
      (OX ω) (OZ ω) (hx ω) (hz ω) χ
  rw [hcongr]
  have hs : (0 : ℝ) ≤ Real.sqrt (c₂ + c₃) := Real.sqrt_nonneg _
  have hfinal : 16 * (16 * δ) ≤ 1024 * (c₁ + Real.sqrt (c₂ + c₃)) := by
    rw [hδdef]
    nlinarith
  exact le_trans (mul_le_mul_of_nonneg_left hproj (by norm_num)) hfinal

end WinImplications

end

end MIPStarRE.QPBT
