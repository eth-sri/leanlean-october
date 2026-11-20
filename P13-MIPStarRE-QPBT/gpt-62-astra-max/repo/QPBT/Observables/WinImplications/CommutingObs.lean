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

local instance pauliEdgeNonemptyCommObs : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-! ## Algebraic preliminaries -/

/-- The left tensor placement is homogeneous in its left factor.
Formalization-only support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem heteroKron_smul_left {ιA ιB : Type*} (c : ℂ) (M : Op ιA) (B : Op ιB) :
    heteroKron (c • M) B = c • heteroKron M B := by
  ext i j
  simp [heteroKron, mul_assoc]

section

variable {P : AdmissibleParams} {X β ι : Type*} {ε : ℝ} (S : ProjectiveSetting P ε) [Fintype β]
  [Fintype ι] [DecidableEq ι] (side : PlayerSide) (W : PauliKind)

/-- The commutator of two reflections written as `1 - 2P` is four times the
commutator of the projections. This is the algebra of Equation `eq:lc-12`,
paper `14_analysis_of_the_pauli_basis_test.tex:330-341`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem reflection_commutator_eq
    (A B : Op ι) :
    (1 - (2 : ℂ) • A) * (1 - (2 : ℂ) • B) -
        (1 - (2 : ℂ) • B) * (1 - (2 : ℂ) • A) =
      (4 : ℂ) • (A * B - B * A) := by
  have h2 : ∀ M : Op ι, (2 : ℂ) • M = M + M := two_smul ℂ
  have h4 : ∀ M : Op ι, (4 : ℂ) • M = M + M + (M + M) := by
    intro M
    rw [show (4 : ℂ) = 2 + 2 by norm_num, add_smul, h2]
  simp_all
  noncomm_ring

/-- The strategy point observable is the reflection about the trace-coarse
grained point projection at label one. This is the first display of
Equation `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-336`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pointObs_eq_one_sub_two_smul
    (r : PauliScalar P) (u : PauliPoint P) :
    S.pointObs side W r u =
      1 - (2 : ℂ) • (S.pointTraceMeas side W u r).effect 1 := by
  classical
  rw [pointObs_eq_traceMeas_obs, sum_zmod_two]
  have hsum : (S.pointTraceMeas side W u r).effect 0 +
      (S.pointTraceMeas side W u r).effect 1 = 1 := by
    have := (S.pointTraceMeas side W u r).sum_eq_one
    rwa [sum_zmod_two] at this
  have hzero : phaseSign 0 = 1 := phaseSign.eq_1 0
  have hone : phaseSign 1 = -1 := phaseSign.eq_1 1
  simp_all
  simp [← hsum, two_smul] <;> abel

/-! ## Pair/W self-consistency on commuting tuples -/

/-- Pair/W self-consistency is the Pair/W self-loop label mismatch. This is
item 1 of `lem:qld-win-implications` read on the Pair/W questions, paper
`14_analysis_of_the_pauli_basis_test.tex:197-199,315-320`, blueprint
`ch14_qpbt_observables.tex:633-637`. -/
theorem pairWConsistency_eq_mismatch :
    bipartiteDefect (commTupleDist P)
        (fun ω => S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (fun ω => S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        S.toStrategy.ψ =
      avgOver (commTupleDist P) (fun ω =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (ProjectiveSetting.pairWQuestion P W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
          (fun A B => ProjectiveSetting.pairWAnswerOrZero A ≠
            ProjectiveSetting.pairWAnswerOrZero B)) := by
  rw [← consistencyDefect_postprocess_eq_mismatch]
  rfl

/-- The Pair/W measurements are self-consistent on commuting tuples. This is
item 1 of `lem:qld-win-implications` on the Pair/W questions, used in the
chain leading to Equation `eq:lc-11`, paper
`14_analysis_of_the_pauli_basis_test.tex:315-320`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pairW_self_consistency_comm_le :
    bipartiteDefect (commTupleDist P)
        (fun ω => S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        (fun ω => S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
        S.toStrategy.ψ ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  classical
  rw [pairWConsistency_eq_mismatch]
  calc
    _ ≤ _ := by
      apply avgOver_comm_le_two_mul_gated
      intro ω
      apply outcome_event_weight_nonneg
    _ ≤ 2 * avgOver (uniformDistribution (PauliSpace P))
        (pauliRejectionAt S.toStrategy (pauliLoopEdge (.pairW W))) := by
      gcongr
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
        grind
      rw [pauliCL_shared_eq P (.pairW W) rfl] at hs
      by_cases hcomm : IsCommuting (pauliSharedSplit P z).1
      · simp_all
        exact hs
      · simp_all
        apply pauliRejectionAt_nonneg
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fixedEdgeRejection_le_error S _)
        (by norm_num)

/-! ## The chained relation of Equation `eq:lc-11` -/

/-- Chaining the commuting-case consistency relations gives the point/Pair
relation `eq:lc-11`. The statement is generic in the two tensor factors and in
the state, so that both orientations of `eq:pts-obs-commutation` use it. Paper
`14_analysis_of_the_pauli_basis_test.tex:311-322`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pointTrace_pairComponent_dist_le
    {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    {MP QL : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιL}
    {QR RR : PauliTuple P → MIPStarRE.Quantum.Measurement (ZMod 2) ιR}
    {χ : EuclideanSpace ℂ (ιL × ιR)} (hχ : ‖χ‖ = 1) {c₁ c₂ c₃ : ℝ}
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
  exact opFamilyDistSq_placed_le_of_consistencyDefect_le (consistencyDefect_trans_le _
      (fun ω => DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (MP ω))
      (fun ω => DistanceCalculus.rightPlacedMeasurement (QR ω))
      (fun ω => DistanceCalculus.leftPlacedMeasurement (QL ω))
      (fun ω => DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (RR ω))
      χ c₁ c₂ c₃ (commTupleDist_isProbability P) hχ h1 h2 h3)

/-! ## The commutation analysis on commuting tuples -/

/-- Padding an answer alphabet by a unit factor does not change the operator
distance. Formalization-only support for `lem:commutation-analysis`, blueprint
`ch12_qpbt_games.tex:418-431`. -/
theorem opFamilyDistSq_unit_prod
    (μ : Distribution X) (M N : X → β → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ (fun x (ub : Unit × β) => M x ub.2)
        (fun x (ub : Unit × β) => N x ub.2) ψ = opFamilyDistSq μ M N ψ := by
  unfold opFamilyDistSq
  congr 1
  funext x
  rw [Fintype.sum_prod_type]
  simp

end

/-- Relabelling the outcomes of a measurement along the inclusion into a
one-point product leaves every effect unchanged. Formalization-only support for
`lem:commutation-analysis`, blueprint `ch12_qpbt_games.tex:418-431`. -/
theorem unitProd_postprocess_effect {β ι : Type*} [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (M : MIPStarRE.Quantum.Measurement β ι)
    (b : β) :
    (M.postprocess (fun b' : β => ((), b'))).effect ((), b) = M.effect b := by
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [show (Finset.univ.filter
      (fun b' : β => ((), b') = ((), b))) = {b} from by
    ext b'
    simp]
  apply Finset.sum_singleton

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
  classical
  intro P ιL ιR _ _ _ _ MX MZ N χ δ hN hX hZ
  set A : PauliTuple P →
      MIPStarRE.Quantum.Measurement (Unit × ZMod 2) ιL := fun ω =>
    (MX ω).postprocess (fun b => ((), b)) with hAdef
  set D : PauliTuple P →
      MIPStarRE.Quantum.Measurement (Unit × ZMod 2) ιL := fun ω =>
    (MZ ω).postprocess (fun c => ((), c)) with hDdef
  set B : PauliTuple P →
      MIPStarRE.Quantum.Measurement ((Unit × ZMod 2) × ZMod 2) ιR := fun ω =>
    (N ω).postprocess (fun bits => (((), bits.1), bits.2)) with hBdef
  have hAB : opFamilyDistSq (commTupleDist P)
      (fun ω ab => heteroKron ((A ω).effect ab) 1)
      (fun ω ab => heteroKron 1
        (((B ω).postprocess (fun abc => abc.1)).effect ab)) χ ≤ δ := by
    have hrw : opFamilyDistSq (commTupleDist P)
        (fun ω ab => heteroKron ((A ω).effect ab) 1)
        (fun ω ab => heteroKron 1
          (((B ω).postprocess (fun abc => abc.1)).effect ab)) χ =
      opFamilyDistSq (commTupleDist P)
        (fun ω ub => heteroKron
          ((MX ω).effect ub.2) 1)
        (fun ω (ub : Unit × ZMod 2) => heteroKron 1
          (((N ω).postprocess (fun bits => bits.1)).effect ub.2)) χ := by
      congr 1 <;> funext ω ab
      · obtain ⟨⟨⟩, b⟩ := ab
        rw [unitProd_postprocess_effect]
      · obtain ⟨⟨⟩, b⟩ := ab
        rw [hBdef, MIPStarRE.Quantum.Measurement.postprocess_comp, MIPStarRE.Quantum.Measurement.postprocess_effect,
          MIPStarRE.Quantum.Measurement.postprocess_effect]
        simp
    refine le_of_eq_of_le hrw ?_
    exact hX
  have hDB : opFamilyDistSq (commTupleDist P)
      (fun ω ac => heteroKron ((D ω).effect ac) 1)
      (fun ω ac => heteroKron 1
        (((B ω).postprocess (fun abc => (abc.1.1, abc.2))).effect ac))
      χ ≤ δ := by
    have hrw : opFamilyDistSq (commTupleDist P)
        (fun ω ac => heteroKron ((D ω).effect ac) 1)
        (fun ω ac => heteroKron 1
          (((B ω).postprocess (fun abc => (abc.1.1, abc.2))).effect ac))
        χ =
      opFamilyDistSq (commTupleDist P)
        (fun ω ub => heteroKron
          ((MZ ω).effect ub.2) 1)
        (fun ω (ub : Unit × ZMod 2) => heteroKron 1
          (((N ω).postprocess (fun bits => bits.2)).effect ub.2)) χ := by
      congr 1 <;> funext ω ac
      · obtain ⟨⟨⟩, c⟩ := ac
        rw [unitProd_postprocess_effect]
      · obtain ⟨⟨⟩, c⟩ := ac
        rw [hBdef, MIPStarRE.Quantum.Measurement.postprocess_comp, MIPStarRE.Quantum.Measurement.postprocess_effect,
          MIPStarRE.Quantum.Measurement.postprocess_effect]
        simp
    refine le_of_eq_of_le hrw ?_
    apply hZ
  have hout := op_dist_sq_commutator_le_explicit
    _ A B D χ δ (by
      intro ω
      solve_by_elim [SandwichProduct.postprocess_isProjective]) hAB hDB
  refine le_trans ?_ hout
  apply avgOver_mono
  intro ω
  simp
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum
    (fun _ _ => by positivity) (Finset.mem_univ (((), 1), 1)))
  rw [hAdef, hDdef]
  simp only [unitProd_postprocess_effect]

/-! ## From projections to observables -/

/-- Applying a scaled operator scales the resulting state. Formalization-only
support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem applyOperatorToState_smul_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (M : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (c • M) v = c • applyOperatorToState M v := by
  unfold applyOperatorToState
  simp

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
  have hproj := point_trace_commutator_comm_le_explicit MX MZ N χ hp (pointTrace_pairComponent_dist_le hn a1 b1 d1) (pointTrace_pairComponent_dist_le hn a2 b2 d2)
  have hcongr : avgOver (commTupleDist P) (fun ω =>
      ‖applyOperatorToState
        (heteroKron (OX ω * OZ ω) 1 -
          heteroKron (OZ ω * OX ω) 1) χ‖ ^ 2) =
    16 * avgOver (commTupleDist P) (fun ω =>
      ‖applyOperatorToState (heteroKron
        ((MX ω).effect 1 * (MZ ω).effect 1 -
          (MZ ω).effect 1 * (MX ω).effect 1) 1) χ‖ ^ 2) := by
    rw [← avgOver_const_mul]
    refine avgOver_congr _ _ _ (fun ω => ?_)
    rw [← heteroKron_sub_left, (hx ω), (hz ω), reflection_commutator_eq,
      heteroKron_smul_left, applyOperatorToState_smul_op, norm_smul]
    simp <;> ring
  linarith

end WinImplications

end

end MIPStarRE.QPBT
