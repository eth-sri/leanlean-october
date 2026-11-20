module

public import QPBT.Observables.LineMeasurement.SelfConsistency
public import QPBT.Observables.LineMeasurement.Evaluation
public import QPBT.Observables.ExpandedReadout

/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Effects of the completed measurement families -/

section

variable (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : PauliPoint P)
include S side W u

/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some
    (b : PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b :=
  SandwichProduct.postprocess_some_effect _ b

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none :
    (S.pointMeasExpOption side W u).effect none = 0 :=
  SandwichProduct.postprocess_some_effect_none _

end

open DistanceCalculus

private def optionShift (x : Option (PauliScalar P) × PauliScalar P) : Option (PauliScalar P) :=
  x.1.map (· + x.2)

private theorem evalOpt_add_map {L : LdParams} {c : ℕ} {line : LineDesc L}
    {u : LdPoint L} (f : DegPoly L c) {g : DegPoly L c} {b : ScalarQ L}
    (hg : evalOpt line u g = some b) :
    evalOpt line u (f + g) = (evalOpt line u f).map (· + b) := by
  cases hf : evalOpt line u f with
  | some a => exact evalOpt_add_of_some hf hg
  | none =>
    cases hsum : evalOpt line u (f + g) with
    | none => rfl
    | some a =>
      have hh := evalOpt_left_of_add_some hsum hg
      rw [hf] at hh
      cases hh

section

variable (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind)
include S side W

private theorem lineEvalMeasExp_eq_shift (line : LineDesc P.toLdParams) (u : PauliPoint P)
    (hu : u ∈ line.pointSet) :
    S.lineEvalMeasExp side W line u =
      (tensorMeasurement (S.lineEvalMeas side W line u) (tauPointMeas W u)).postprocess optionShift := by
  rw [lineEvalMeasExp, lineMeasExp, tauLineMeas, tensorMeasurement_postprocess_right,
    lineEvalMeas, tauPointMeas, tensorMeasurement_postprocess]
  simp only [Quantum.Measurement.postprocess_comp]
  congr 1
  funext ⟨f, h⟩
  exact evalOpt_add_map f (evalOpt_restrictToLine_lowDegreeEncoding _ line h u hu)

private theorem pointMeasExpOption_eq_shift (u : PauliPoint P) :
    S.pointMeasExpOption side W u =
      (tensorMeasurement (S.pointMeasOption side W u) (tauPointMeas W u)).postprocess optionShift := by
  have h := Quantum.Measurement.ext (S.pointMeasExp_effect_eq_pointTauMeas_postprocess side W u)
  rw [pointMeasExpOption, h, pointTauMeas, pointMeasOption, tensorMeasurement_postprocess_left]
  simp only [Quantum.Measurement.postprocess_comp]
  rfl

end

private theorem noEvaluation_effect {I : Type*} [Fintype I] [DecidableEq I]
    (line : LineDesc P.toLdParams) {u : PauliPoint P} (hu : u ∉ line.pointSet)
    (M : Measurement (PauliLinePoly P) I) (a : PauliScalar P) :
    (M.postprocess (evalOpt line u)).effect (some a) = 0 := by
  rw [Quantum.Measurement.postprocess_effect]
  simp [evalOpt_eq_none_of_not_mem hu]

set_option maxHeartbeats 1000000 in
-- Elaborate the mixed point/line effect families before collapsing their fibers.
/-- On evaluating samples, the ancillary Pauli readouts, after evaluation,
are identical. They shift both strategy answers by the same amount, preserving
agreement even with a `none` outcome. Off the line the whole overlap is zero. -/
theorem sum_stateQForm_evalClass_placement_eq (S : ProjectiveSetting P ε) (p : Placement)
    (W : PauliKind) (line : LineDesc P.toLdParams) (u : PauliPoint P) :
    (∑ o, S.placedCorrelation p (overlapPartner p) ((S.lineEvalMeasExp p.side W line u).effect o) ((S.pointMeasExpOption (overlapPartner p).side W u).effect o)) =
    ∑ o, strategyOverlap S p ((S.lineEvalMeas p.side W line u).effect o)
      ((S.pointMeasOption (overlapPartner p).side W u).effect o) := by
  classical
  by_cases hu : u ∈ line.pointSet
  · rw [S.lineEvalMeasExp_eq_shift _ W line u hu, S.pointMeasExpOption_eq_shift]
    exact S.placed_shift_overlap p W u _ _ (fun a c => optionShift (a, c)) (by
      intro c a b h
      cases a <;> cases b <;> simp_all [optionShift])
  · have hleft (a : PauliScalar P) : (S.lineEvalMeasExp p.side W line u).effect (some a) = 0 :=
      noEvaluation_effect line hu _ a
    have hright (a : PauliScalar P) : (S.lineEvalMeas p.side W line u).effect (some a) = 0 :=
      noEvaluation_effect line hu _ a
    have hnone : (S.pointMeasOption (overlapPartner p).side W u).effect none = 0 := by
      rw [pointMeasOption, Quantum.Measurement.postprocess_effect]
      simp
    trans 0
    · apply Finset.sum_eq_zero
      rintro (_ | a) _ <;> simp [S.pointMeasExpOption_effect_none, hleft, placedCorrelation, S.place_zero, stateQForm_zero]
    · symm
      apply Finset.sum_eq_zero
      rintro (_ | a) _
      · rw [hnone]
        cases p <;> simp [strategyOverlap, heteroKron_zero_left, heteroKron_zero_right, stateQForm_zero]
      · rw [hright]
        cases p <;> simp [strategyOverlap, heteroKron_zero_left, heteroKron_zero_right, stateQForm_zero]

end ProjectiveSetting

end

end MIPStarRE.QPBT
