module

public import QPBT.Observables.WinImplications.Setup

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
  rw [avgOver_uniform_prod]
  have hsum : (Fintype.card X : ℝ) *
      avgOver (uniformDistribution X)
        (fun x => avgOver (uniformDistribution Y) (f x)) =
      ∑ x : X, avgOver (uniformDistribution Y) (f x) := by
    unfold avgOver uniformDistribution Distribution.uniformOnFinset
    simp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    field_simp
  rw [hsum]
  exact Finset.single_le_sum
    (fun x _ => avgOver_nonneg (uniformDistribution Y) (f x) (hf x))
    (Finset.mem_univ x0)

variable {X : Type*}

/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
a finite distribution average may be extended to the full finite type. -/
theorem avgOver_eq_sum_univ [Fintype X]
    (μ : Distribution X) (f : X → ℝ) :
    avgOver μ f = ∑ x : X, μ.weight x * f x := by
  exact (Distribution.sum_univ_eq_sum_support μ (fun x => μ.weight x * f x)
    (fun x hx => by rw [μ.outsideSupport x hx, zero_mul])).symm

/-- Formalization-only auxiliary for item 2 of `lem:qld-win-implications`:
averaging against a convex mixture is the corresponding convex combination. -/
theorem avgOver_mix [Finite X] [DecidableEq X]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : Distribution X) (f : X → ℝ) :
    avgOver (Distribution.mix t ht0 ht1 μ ν) f =
      t * avgOver μ f + (1 - t) * avgOver ν f := by
  letI := Fintype.ofFinite X
  rw [avgOver_eq_sum_univ, avgOver_eq_sum_univ, avgOver_eq_sum_univ]
  simp [Distribution.mix, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Formalization-only auxiliary for items 4–7 of `lem:qld-win-implications`:
conditioning a uniform law divides its gated ambient average by the event probability. -/
theorem cardRatio_mul_avgOver_filter
    [Fintype X] [DecidableEq X] [Nonempty X]
    (p : X → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).Nonempty)
    (f : X → ℝ) :
    ((Finset.univ.filter p).card : ℝ) / Fintype.card X *
        avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      avgOver (uniformDistribution X) (fun x => if p x then f x else 0) := by
  unfold avgOver uniformDistribution
  simp only [Distribution.uniformOnFinset_support,
    Distribution.uniformOnFinset_weight, Finset.mem_filter, Finset.mem_univ,
    true_and, if_true]
  rw [Finset.card_univ, Finset.sum_congr rfl fun x hx => by
    rw [if_pos (Finset.mem_filter.1 hx).2], ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_filter]
  field_simp

/-- Conditioning on the commuting event costs at most its reciprocal lower bound. -/
theorem avgOver_comm_le_two_mul_gated (P : AdmissibleParams)
    (f : PauliTuple P → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    avgOver (commTupleDist P) f ≤
      2 * avgOver (uniformDistribution (PauliTuple P))
        (fun ω => if IsCommuting ω then f ω else 0) := by
  have hnonempty : (Finset.univ.filter (@IsCommuting P)).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [IsCommuting, gammaValue, fixedBinTrace, binTrace, dotProduct]
  have heq := cardRatio_mul_avgOver_filter (@IsCommuting P) hnonempty f
  change commProb P * avgOver (commTupleDist P) f = _ at heq
  have havg :=
    avgOver_nonneg (commTupleDist P) f hf
  nlinarith [commProb_ge_half P]

/-- Conditioning on the anticommuting event costs at most sixteen. -/
theorem avgOver_anticomm_le_sixteen_mul_gated (P : AdmissibleParams)
    (f : PauliTuple P → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    avgOver (anticommTupleDist P) f ≤
      16 * avgOver (uniformDistribution (PauliTuple P))
        (fun ω => if IsAnticommuting ω then f ω else 0) := by
  have hnonempty : (Finset.univ.filter (@IsAnticommuting P)).Nonempty := by
    by_contra h
    have hempty : Finset.univ.filter (@IsAnticommuting P) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    have hprob := anticommTupleDist_isProbability P
    unfold anticommTupleDist Distribution.IsProbability Distribution.totalWeight at hprob
    rw [hempty] at hprob
    simp at hprob
  have heq := cardRatio_mul_avgOver_filter (@IsAnticommuting P) hnonempty f
  change anticommProb P * avgOver (anticommTupleDist P) f = _ at heq
  have hqpos : 0 < P.q := zero_lt_two.trans_le P.hq.two_le
  have hmq := Nat.le_of_dvd hqpos P.hdvd
  have hprob := anticommProb_ge_of_m_le_q P hmq
  norm_num at hprob
  have havg :=
    avgOver_nonneg (anticommTupleDist P) f hf
  nlinarith

variable {G : Game}

/-- Formalization-only auxiliary for items 1–5 and 7 of `lem:qld-win-implications`:
inconsistency of two postprocessed strategy measurements is the Born mass
of source outcomes whose postprocessed labels differ. -/
theorem consistencyDefect_postprocess_eq_mismatch
    {X β : Type*} [Fintype X] [DecidableEq X]
    [Fintype β] [DecidableEq β]
    (μ : Distribution X) (S : Strategy G)
    (qA : X → G.QuestionA) (qB : X → G.QuestionB)
    (fA : X → G.AnswerA → β) (fB : X → G.AnswerB → β) :
    consistencyDefect μ
        (fun x c => heteroKron (((S.A (qA x)).postprocess (fA x)).effect c) 1)
        (fun x c => heteroKron 1 (((S.B (qB x)).postprocess (fB x)).effect c))
        S.ψ =
      avgOver μ (fun x => outcomeEventWeight S (qA x) (qB x)
        (fun a b => fA x a ≠ fB x b)) := by
  refine avgOver_congr _ _ _ fun x => ?_
  simp only [DistanceCalculus.consistency_term_eq_stateQForm,
    MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp_rw [DistanceCalculus.placed_product_stateQForm_eq,
    DistanceCalculus.heteroKron_finset_sum_left, DistanceCalculus.heteroKron_finset_sum_right,
    DistanceCalculus.stateQForm_finset_sum, Finset.sum_filter, outcomeEventWeight]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  symm
  calc _ = ∑ p : G.AnswerA × G.AnswerB, ∑ q : β × β, if fA x p.1 = q.1 ∧ fB x p.2 = q.2 ∧
        q.1 ≠ q.2 then outcomeWeight S (qA x) (qB x) p.1 p.2 else 0 :=
      Fintype.sum_congr _ _ fun p => by simp [Fintype.sum_prod_type, ite_and]
    _ = _ := Finset.sum_comm.trans (Fintype.sum_congr _ _ fun q => by
      rw [Fintype.sum_prod_type]; by_cases h : q.1 = q.2 <;> simp [h, ite_and]; rfl)

/-- The question pair generated by a fixed ordered Pauli edge and seed. -/
def pauliSourceQuestions (P : AdmissibleParams) (e : PauliEdge)
    (z : PauliSpace P) : PauliQuestion P × PauliQuestion P :=
  ((e.1.1, pauliCL P e.1.1 z), (e.1.2, pauliCL P e.1.2 z))

/-- Rejection mass at a fixed ordered Pauli edge and seed. -/
noncomputable def pauliRejectionAt {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (e : PauliEdge) (z : PauliSpace P) : ℝ :=
  let questions := pauliSourceQuestions P e z
  outcomeEventWeight S questions.1 questions.2 fun a b =>
    (pauliBasisTest P).decide questions.1 questions.2 a b = false

/-- Rejection mass at every fixed edge and seed is nonnegative. -/
theorem pauliRejectionAt_nonneg {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (e : PauliEdge) (z : PauliSpace P) :
    0 ≤ pauliRejectionAt S e z :=
  outcome_event_weight_nonneg S _ _ _

/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
the average rejection mass of a finite game is one minus its value. -/
theorem rejectionEventAverage_eq_one_sub_value (S : Strategy G) :
    avgOver G.μ (fun questions =>
      outcomeEventWeight S questions.1 questions.2 fun a b =>
        G.decide questions.1 questions.2 a b = false) =
      1 - S.value := by
  simpa only [outcomeEventWeight, Bool.eq_false_iff, ite_not] using
    MIPStarRE.QPBT.rejectionMass_eq_one_sub_value S

/-- A strategy winning with probability at least `1 - ε` has average Pauli-edge
rejection probability at most `ε`. -/
theorem pauliRejectionAverage_le_error_of_win {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) :
    avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt S ez.1 ez.2) ≤ ε := by
  refine le_of_eq_of_le ?_ (by linarith : 1 - S.value ≤ ε)
  rw [← rejectionEventAverage_eq_one_sub_value S]
  unfold pauliBasisTest pauliQuestionDistribution
  rw [Distribution.avgOver_map]
  rfl

/-- Rejection on one fixed oriented edge is at most the number of edge types
times the total rejection probability. -/
theorem fixedEdgeRejection_le_error_of_win {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (e : PauliEdge) :
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S e) ≤
      (Fintype.card PauliEdge : ℝ) * ε :=
  (avgOver_uniform_fixed_le_card_mul_prod _ (pauliRejectionAt_nonneg S) e).trans
    (mul_le_mul_of_nonneg_left (pauliRejectionAverage_le_error_of_win S hwin) (Nat.cast_nonneg _))

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)

/-- Fixing one verifier edge costs at most the cardinality of the finite edge graph. -/
theorem fixedEdgeRejection_le_error (e : PauliEdge) :
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S.toStrategy e) ≤
      (Fintype.card PauliEdge : ℝ) * ε :=
  fixedEdgeRejection_le_error_of_win S.toStrategy S.win e

end WinImplications

end

end MIPStarRE.QPBT
