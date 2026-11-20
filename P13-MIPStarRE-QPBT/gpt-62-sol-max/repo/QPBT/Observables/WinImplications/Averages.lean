module

public import QPBT.Observables.WinImplications.Setup
public import QPBT.Games.DistributionAux

/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The formalization-only averaging and conditioning auxiliaries support items 1–7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

open DistanceCalculus

scoped instance pauliEdgeNonempty : Nonempty PauliEdge := pauliEdge_nonempty

/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
a fixed component of a nonnegative uniform product average is bounded by
the cardinality of the first factor times the full average. -/
theorem avgOver_uniform_fixed_le_card_mul_prod
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (f : X → Y → ℝ) (hf : ∀ x y, 0 ≤ f x y) (x0 : X) :
    avgOver (uniformDistribution Y) (f x0) ≤
      (Fintype.card X : ℝ) *
        avgOver (uniformDistribution (X × Y)) (fun xy => f xy.1 xy.2) := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [avgOver_uniform_prod, avgOver_uniform_eq_inv_card_mul_sum (α := X), ← mul_assoc,
    mul_inv_cancel₀ hc, one_mul]
  exact Finset.single_le_sum (fun x _ => avgOver_nonneg _ _ (hf x)) (Finset.mem_univ x0)

section

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (p : X → Prop) [DecidablePred p]
include X p

/-- Formalization-only auxiliary for items 4–7 of `lem:qld-win-implications`:
conditioning a uniform law divides its gated ambient average by the event probability. -/
theorem cardRatio_mul_avgOver_filter (hp : (Finset.univ.filter p).Nonempty)
    (f : X → ℝ) :
    ((Finset.univ.filter p).card : ℝ) / Fintype.card X *
        avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      avgOver (uniformDistribution X) (fun x => if p x then f x else 0) := by
  have hp0 : ((Finset.univ.filter p).card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hp
  rw [avgOver_uniformOnFinset_eq_inv_card_mul_sum, avgOver_uniform_eq_inv_card_mul_sum,
    ← Finset.sum_filter]
  field_simp

/-- A lower bound on the probability of an event controls the cost of conditioning. -/
private theorem avgOver_filtered_le_gated (c : ℝ)
    (hc : 1 ≤ c * (((Finset.univ.filter p).card : ℝ) / Fintype.card X))
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f ≤
      c * avgOver (uniformDistribution X) (fun x => if p x then f x else 0) := by
  have hp : (Finset.univ.filter p).Nonempty := by
    by_contra h
    norm_num [Finset.not_nonempty_iff_eq_empty.mp h] at hc
  rw [← cardRatio_mul_avgOver_filter p hp f, ← mul_assoc]
  exact le_mul_of_one_le_left (avgOver_nonneg _ _ hf) hc

end

section

variable (P : AdmissibleParams)
    (f : PauliTuple P → ℝ) (hf : ∀ ω, 0 ≤ f ω)
include P f hf

/-- Conditioning on commuting tuples costs at most two. -/
theorem avgOver_comm_le_two_mul_gated :
    avgOver (commTupleDist P) f ≤
      2 * avgOver (uniformDistribution (PauliTuple P))
        (fun ω => if IsCommuting ω then f ω else 0) := by
  refine avgOver_filtered_le_gated _ _ ?_ f hf
  change 1 ≤ 2 * commProb P
  linarith [commProb_ge_half P]

/-- Conditioning on anticommuting tuples costs at most sixteen. -/
theorem avgOver_anticomm_le_sixteen_mul_gated :
    avgOver (anticommTupleDist P) f ≤
      16 * avgOver (uniformDistribution (PauliTuple P))
        (fun ω => if IsAnticommuting ω then f ω else 0) := by
  refine avgOver_filtered_le_gated _ _ ?_ f hf
  change 1 ≤ 16 * anticommProb P
  have hq := P.hq.two_le
  have h := anticommProb_ge_of_m_le_q P (Nat.le_of_dvd (by omega) P.hdvd)
  norm_num at h
  linarith

end

/-- Formalization-only auxiliary for items 1–5 and 7 of `lem:qld-win-implications`:
inconsistency of two postprocessed strategy measurements is the Born mass
of source outcomes whose postprocessed labels differ. -/
theorem consistencyDefect_postprocess_eq_mismatch
    {G : Game} {X β : Type*} [Fintype X] [DecidableEq X]
    [Fintype β] [DecidableEq β]
    (μ : Distribution X) (S : Strategy G)
    (qA : X → G.QuestionA) (qB : X → G.QuestionB)
    (fA : X → G.AnswerA → β) (fB : X → G.AnswerB → β) :
    bipartiteDefect μ
        (fun x => (S.A (qA x)).postprocess (fA x))
        (fun x => (S.B (qB x)).postprocess (fB x))
        S.ψ =
      avgOver μ (fun x => outcomeEventWeight S (qA x) (qB x)
        (fun a b => fA x a ≠ fB x b)) := by
  unfold bipartiteDefect consistencyDefect
  apply avgOver_congr
  intro x
  simp only [placed_product_stateQForm_eq,
    outcomeEventWeight, ite_not]
  exact point_placed_defect_postprocess (S.A (qA x)) (S.B (qB x)) S.ψ (fA x) (fB x)

/-- The question pair generated by a fixed ordered Pauli edge and seed. -/
def pauliSourceQuestions (P : AdmissibleParams) (e : PauliEdge)
    (z : PauliSpace P) : PauliQuestion P × PauliQuestion P :=
  ((e.1.1, pauliCL P e.1.1 z), (e.1.2, pauliCL P e.1.2 z))

section

variable {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (e : PauliEdge) (z : PauliSpace P)

/-- Rejection mass at a fixed ordered Pauli edge and seed. -/
noncomputable def pauliRejectionAt : ℝ :=
  let questions := pauliSourceQuestions P e z
  outcomeEventWeight S questions.1 questions.2 fun a b =>
    (pauliBasisTest P).decide questions.1 questions.2 a b = false

/-- A disagreement of extracted labels implies rejection whenever accepted
answers carry identical labels. -/
theorem mismatch_le_pauliRejectionAt {P : AdmissibleParams} {α : Type*} [DecidableEq α]
    (S : Strategy (pauliBasisTest P)) (e : PauliEdge) (z : PauliSpace P)
    (f g : PauliAnswer P → α)
    (h : ∀ a b, pauliWinPredicate P (pauliSourceQuestions P e z).1
      (pauliSourceQuestions P e z).2 a b = true → f a = g b) :
    outcomeEventWeight S (pauliSourceQuestions P e z).1 (pauliSourceQuestions P e z).2
      (fun a b => f a ≠ g b) ≤ pauliRejectionAt S e z :=
  outcome_event_weight_mono S _ _ _ _ fun a b hne => Bool.eq_false_iff.mpr (hne ∘ h a b)

/-- Rejection mass at every fixed edge and seed is nonnegative. -/
theorem pauliRejectionAt_nonneg :
    0 ≤ pauliRejectionAt S e z := by
  exact outcome_event_weight_nonneg S _ _ _

end

/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
the average rejection mass of a finite game is one minus its value. -/
theorem rejectionEventAverage_eq_one_sub_value {G : Game} (S : Strategy G) :
    avgOver G.μ (fun questions =>
      outcomeEventWeight S questions.1 questions.2 fun a b =>
        G.decide questions.1 questions.2 a b = false) =
      1 - S.value := by
  classical
  simpa only [outcomeEventWeight, Bool.eq_false_iff, ite_not] using
    MIPStarRE.QPBT.rejectionMass_eq_one_sub_value S

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
include P ε S hwin

/-- A strategy winning with probability at least `1 - ε` has average Pauli-edge
rejection probability at most `ε`. -/
theorem pauliRejectionAverage_le_error_of_win :
    avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt S ez.1 ez.2) ≤ ε := by
  have havg : avgOver (uniformDistribution (PauliEdge × PauliSpace P))
      (fun ez => pauliRejectionAt S ez.1 ez.2) = 1 - S.value := by
    rw [← rejectionEventAverage_eq_one_sub_value S]
    unfold pauliBasisTest pauliQuestionDistribution
    rw [Distribution.avgOver_map]
    rfl
  rw [havg]
  linarith

/-- Rejection on one fixed oriented edge is at most the number of edge types
times the total rejection probability. -/
theorem fixedEdgeRejection_le_error_of_win (e : PauliEdge) :
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S e) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  calc
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S e) ≤
        (Fintype.card PauliEdge : ℝ) *
          avgOver (uniformDistribution (PauliEdge × PauliSpace P))
            (fun ez => pauliRejectionAt S ez.1 ez.2) := by
      exact avgOver_uniform_fixed_le_card_mul_prod _
        (fun edge z => pauliRejectionAt_nonneg S edge z) e
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_left (pauliRejectionAverage_le_error_of_win S hwin)
        (Nat.cast_nonneg _)

end

/-- Fixing one verifier edge costs at most the number of ordered edges. -/
theorem fixedEdgeRejection_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (e : PauliEdge) :
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S.toStrategy e) ≤
      (Fintype.card PauliEdge : ℝ) * ε :=
  fixedEdgeRejection_le_error_of_win S.toStrategy S.win e

end WinImplications

end

end MIPStarRE.QPBT
