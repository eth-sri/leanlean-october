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

/-- The left tensor placement is homogeneous in its left factor.
Formalization-only support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem heteroKron_smul_left {ιA ιB : Type*} (c : ℂ) (M : Op ιA) (B : Op ιB) :
    heteroKron (c • M) B = c • heteroKron M B := by
  ext i j
  simp [heteroKron, Matrix.kronecker, mul_assoc]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The commutator of two reflections written as `1 - 2P` is four times the
commutator of the projections. This is the algebra of Equation `eq:lc-12`,
paper `14_analysis_of_the_pauli_basis_test.tex:330-341`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem reflection_commutator_eq (A B : Op ι) :
    (1 - (2 : ℂ) • A) * (1 - (2 : ℂ) • B) -
        (1 - (2 : ℂ) • B) * (1 - (2 : ℂ) • A) =
      (4 : ℂ) • (A * B - B * A) := by
  have h2 : ∀ M : Op ι, (2 : ℂ) • M = M + M := fun M => two_smul ℂ M
  have h4 : ∀ M : Op ι, (4 : ℂ) • M = M + M + (M + M) := by
    intro M
    rw [show (4 : ℂ) = 2 + 2 by norm_num, add_smul, h2]
  rw [h2, h2, h4]
  noncomm_ring

variable {P : AdmissibleParams} {ε : ℝ}

/-- The strategy point observable is the reflection about the trace-coarse
grained point projection at label one. This is the first display of
Equation `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-336`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pointObs_eq_one_sub_two_smul (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u =
      1 - (2 : ℂ) • (S.pointTraceMeas side W u r).effect 1 := by
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

/-- The Pair/W measurements are self-consistent on commuting tuples. This is
item 1 of `lem:qld-win-implications` on the Pair/W questions, used in the
chain leading to Equation `eq:lc-11`, paper
`14_analysis_of_the_pauli_basis_test.tex:315-320`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pairW_self_consistency_comm_le (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.toStrategy.ψ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  refine (consistencyDefect_postprocess_eq_mismatch (commTupleDist P) S.toStrategy
    (fun ω => ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) _
    (fun _ => ProjectiveSetting.pairWAnswerOrZero) fun _ =>
      ProjectiveSetting.pairWAnswerOrZero).trans_le ?_
  refine (avgOver_comm_le_two_mul_gated P _ fun ω =>
    outcome_event_weight_nonneg S.toStrategy _ _ _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (le_trans ?_
    (fixedEdgeRejection_le_error S (pauliLoopEdge (.pairW W)))) (by norm_num)
  rw [← avgOver_pauliTuple_uniform]
  refine avgOver_mono _ _ _ fun z => ?_
  have hs := le_trans (outcome_event_weight_mono _ _ _ _ _ fun A B
    (hne : ProjectiveSetting.pairWAnswerOrZero A ≠ ProjectiveSetting.pairWAnswerOrZero B)
      (hAB : A = B) => hne (by rw [hAB])) (loopMismatch_le_rejection S (.pairW W) z)
  rw [pauliCL_shared_eq P (.pairW W) rfl] at hs
  split_ifs
  · simpa [pauliSharedSplit, ProjectiveSetting.pairWQuestion] using hs
  · exact pauliRejectionAt_nonneg S.toStrategy _ z

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
    (h1 : consistencyDefect (commTupleDist P)
      (fun ω a => heteroKron ((MP ω).effect a) 1)
      (fun ω a => heteroKron 1 ((QR ω).effect a)) χ ≤ c₁)
    (h2 : consistencyDefect (commTupleDist P)
      (fun ω a => heteroKron ((QL ω).effect a) 1)
      (fun ω a => heteroKron 1 ((QR ω).effect a)) χ ≤ c₂)
    (h3 : consistencyDefect (commTupleDist P)
      (fun ω a => heteroKron ((QL ω).effect a) 1)
      (fun ω a => heteroKron 1 ((RR ω).effect a)) χ ≤ c₃) :
    opFamilyDistSq (commTupleDist P)
      (fun ω a => heteroKron ((MP ω).effect a) 1)
      (fun ω a => heteroKron 1 ((RR ω).effect a)) χ ≤
        2 * (c₁ + 2 * Real.sqrt (c₂ + c₃)) := by
  have hchain := consistencyDefect_trans_le (commTupleDist P)
    (fun ω => DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (MP ω))
    (fun ω => DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (QR ω))
    (fun ω => DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (QL ω))
    (fun ω => DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (RR ω))
    χ c₁ c₂ c₃ (commTupleDist_isProbability P) hχ h1 h2 h3
  exact opFamilyDistSq_placed_le_of_consistencyDefect_le (commTupleDist P)
    MP RR χ hchain

/-! ## The commutation analysis on commuting tuples -/

/-- Padding an answer alphabet by a unit factor does not change the operator
distance. Formalization-only support for `lem:commutation-analysis`, blueprint
`ch12_qpbt_games.tex:418-431`. -/
theorem opFamilyDistSq_unit_prod {X β ι : Type*} [Fintype β]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → β → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ (fun x (ub : Unit × β) => M x ub.2)
        (fun x (ub : Unit × β) => N x ub.2) ψ = opFamilyDistSq μ M N ψ := by
  unfold opFamilyDistSq
  congr 1
  funext x
  rw [Fintype.sum_prod_type]
  simp

/-- Relabelling the outcomes of a measurement along the inclusion into a
one-point product leaves every effect unchanged. Formalization-only support for
`lem:commutation-analysis`, blueprint `ch12_qpbt_games.tex:418-431`. -/
theorem unitProd_postprocess_effect {β ι : Type*} [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (M : MIPStarRE.Quantum.Measurement β ι)
    (b : β) :
    (M.postprocess (fun b' : β => ((), b'))).effect ((), b) = M.effect b := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [show (Finset.univ.filter
      (fun b' : β => ((), b') = ((), b))) = {b} from by
    ext b'
    simp]
  exact Finset.sum_singleton _ _

/-- The commutator of the two trace-coarse-grained point projections is small
on commuting tuples. This is Equation `eq:qld-obs-comm`, obtained from
`lem:commutation-analysis`; the statement is generic in the two tensor factors
and in the state. Paper `14_analysis_of_the_pauli_basis_test.tex:322-329`,
blueprint `ch14_qpbt_observables.tex:761-794`. -/
theorem point_trace_commutator_comm_le_explicit :
    ∀ {P : AdmissibleParams} {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL]
        [Fintype ιR] [DecidableEq ιR]
        (MX MZ : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
        (N : PauliTuple P →
          MIPStarRE.Quantum.Measurement (ZMod 2 × ZMod 2) ιR)
        (χ : EuclideanSpace ℂ (ιL × ιR)) {δ : ℝ},
      (∀ ω, MIPStarRE.QPBT.Measurement.IsProjective (N ω)) →
      opFamilyDistSq (commTupleDist P)
          (fun ω b => heteroKron ((MX ω).effect b) 1)
          (fun ω b => heteroKron 1
            (((N ω).postprocess (fun bits => bits.1)).effect b)) χ ≤ δ →
      opFamilyDistSq (commTupleDist P)
          (fun ω b => heteroKron ((MZ ω).effect b) 1)
          (fun ω b => heteroKron 1
            (((N ω).postprocess (fun bits => bits.2)).effect b)) χ ≤ δ →
      avgOver (commTupleDist P) (fun ω =>
        ‖applyOperatorToState (heteroKron
          ((MX ω).effect 1 * (MZ ω).effect 1 -
            (MZ ω).effect 1 * (MX ω).effect 1) 1) χ‖ ^ 2) ≤ 16 * δ := by
  intro P ιL ιR _ _ _ _ MX MZ N χ δ hN hX hZ
  have key (M : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
      (f : ZMod 2 × ZMod 2 → ZMod 2) (g : (Unit × ZMod 2) × ZMod 2 → Unit × ZMod 2)
      (hg : ∀ bits, g (((), bits.1), bits.2) = ((), f bits))
      (h : opFamilyDistSq (commTupleDist P) (fun ω b => heteroKron ((M ω).effect b) 1)
        (fun ω b => heteroKron 1 (((N ω).postprocess f).effect b)) χ ≤ δ) :
      opFamilyDistSq (commTupleDist P)
        (fun ω ab => heteroKron (((M ω).postprocess fun b => ((), b)).effect ab) 1)
        (fun ω ab => heteroKron 1 ((((N ω).postprocess fun bits =>
          (((), bits.1), bits.2)).postprocess g).effect ab)) χ ≤ δ := by
    refine le_of_eq_of_le ?_ ((opFamilyDistSq_unit_prod _ _ _ χ).trans_le h)
    congr 1 <;> funext ω ⟨⟨⟩, b⟩
    · rw [unitProd_postprocess_effect]
    · simp only [MIPStarRE.Quantum.Measurement.postprocess_comp,
        MIPStarRE.Quantum.Measurement.postprocess_effect, hg, Prod.mk.injEq, true_and]
  refine le_trans ?_ (op_dist_sq_commutator_le_explicit (commTupleDist P)
    (fun ω => (MX ω).postprocess fun b => ((), b))
    (fun ω => (N ω).postprocess fun bits => (((), bits.1), bits.2))
    (fun ω => (MZ ω).postprocess fun b => ((), b)) χ δ
    (fun ω => SandwichProduct.postprocess_isProjective _ (hN ω) _)
    (key MX Prod.fst (fun abc => abc.1) (fun _ => rfl) hX)
    (key MZ Prod.snd (fun abc => (abc.1.1, abc.2)) (fun _ => rfl) hZ))
  refine avgOver_mono _ _ _ fun ω => le_of_eq_of_le ?_
    (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ (((), 1), 1)))
  simp only [sub_zero, unitProd_postprocess_effect]

/-! ## From projections to observables -/

/-- Applying a scaled operator scales the resulting state. Formalization-only
support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem applyOperatorToState_smul_op (c : ℂ) (M : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (c • M) v = c • applyOperatorToState M v := by
  unfold applyOperatorToState
  rw [map_smul, LinearMap.smul_apply]

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
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((MX ω).effect a) 1)
        (fun ω a => heteroKron 1 ((VX ω).effect a)) χ ≤ c₁ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((MZ ω).effect a) 1)
        (fun ω a => heteroKron 1 ((VZ ω).effect a)) χ ≤ c₁ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((QX ω).effect a) 1)
        (fun ω a => heteroKron 1 ((VX ω).effect a)) χ ≤ c₂ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((QZ ω).effect a) 1)
        (fun ω a => heteroKron 1 ((VZ ω).effect a)) χ ≤ c₂ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((QX ω).effect a) 1)
        (fun ω a => heteroKron 1
          (((N ω).postprocess (fun bits => bits.1)).effect a)) χ ≤ c₃ →
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron ((QZ ω).effect a) 1)
        (fun ω a => heteroKron 1
          (((N ω).postprocess (fun bits => bits.2)).effect a)) χ ≤ c₃ →
      avgOver (commTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
            heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2) ≤
        1024 * (c₁ + Real.sqrt (c₂ + c₃)) := by
  intro P ιL ιR _ _ _ _ MX MZ QX QZ VX VZ N OX OZ χ c₁ c₂ c₃ hn hc hp hx hz a1 a2 b1 b2 d1 d2
  rw [← avgOver_congr _ _ _ fun ω => (norm_pointObs_commutator_sq ((MX ω).effect 1)
    ((MZ ω).effect 1) (OX ω) (OZ ω) (hx ω) (hz ω) χ).symm, avgOver_const_mul]
  have := point_trace_commutator_comm_le_explicit MX MZ N χ hp
    (pointTrace_pairComponent_dist_le MX QX VX _ χ hn a1 b1 d1)
    (pointTrace_pairComponent_dist_le MZ QZ VZ _ χ hn a2 b2 d2)
  nlinarith

end WinImplications

end

end MIPStarRE.QPBT
