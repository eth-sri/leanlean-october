module

public import QPBT.Games.DistanceTheorems.Calculus
public import QPBT.Games.DistanceTheorems.TensorSupport
public import QPBT.Games.DistanceTheorems.ProjectiveRounding
public import QPBT.Games.DistanceTheorems.RoundingTransport
public import QPBT.Games.StrategyClasses
public import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core

/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

The operator-level inequalities they rest on live in
`MIPStarRE.QPBT.Games.DistanceTheorems.Calculus`.

## References

The source results run from blueprint `fact:agreement` through
`lem:close-strategies-have-close-values`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

section

variable {α β I J : Type*} [Fintype α] [Fintype β]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
include α β I J

/-- The product POVM whose effects are Kronecker products of the two factor effects. -/
noncomputable def tensorMeasurement
    (A : Measurement α I) (B : Measurement β J) :
    Measurement (α × β) (I × J) :=
  Measurement.ofSumEqOne
    (fun ab => heteroKron (A.effect ab.1) (B.effect ab.2))
    (fun ab => MIPStarRE.Quantum.kronecker_nonneg (A.pos ab.1) (B.pos ab.2))
    (by
      rw [Fintype.sum_prod_type]
      simp_rw [← heteroKron_finset_sum_right, B.sum_eq_one, ← heteroKron_finset_sum_left,
        A.sum_eq_one, heteroKron_one_one])

/-- The product of projective measurements is projective. -/
theorem tensorMeasurement_isProjective
    {A : Measurement α I} {B : Measurement β J}
    (hA : Measurement.IsProjective A) (hB : Measurement.IsProjective B) :
    Measurement.IsProjective (tensorMeasurement A B) :=
  fun o => MakingMeasurementsProjective.isProj_kronecker (hA o.1) (hB o.2)

end

/-- Relabeling the two outcomes separately commutes with taking the product POVM. -/
theorem tensorMeasurement_postprocess
    {FirstOutcome SecondOutcome FirstLabel SecondLabel FirstSpace SecondSpace : Type*}
    [Fintype FirstOutcome] [DecidableEq FirstOutcome]
    [Fintype SecondOutcome] [DecidableEq SecondOutcome]
    [Fintype FirstLabel] [DecidableEq FirstLabel]
    [Fintype SecondLabel] [DecidableEq SecondLabel]
    [Fintype FirstSpace] [DecidableEq FirstSpace]
    [Fintype SecondSpace] [DecidableEq SecondSpace]
    (firstMeas : Measurement FirstOutcome FirstSpace)
    (secondMeas : Measurement SecondOutcome SecondSpace)
    (firstMap : FirstOutcome → FirstLabel) (secondMap : SecondOutcome → SecondLabel) :
    tensorMeasurement (firstMeas.postprocess firstMap) (secondMeas.postprocess secondMap) =
      (tensorMeasurement firstMeas secondMeas).postprocess (Prod.map firstMap secondMap) := by
  apply MIPStarRE.Quantum.Measurement.ext
  intro ⟨firstLabel, secondLabel⟩
  change heteroKron
      (∑ first ∈ Finset.univ.filter (fun first => firstMap first = firstLabel),
        firstMeas.effect first)
      (∑ second ∈ Finset.univ.filter (fun second => secondMap second = secondLabel),
        secondMeas.effect second) =
    ∑ outcomes ∈ Finset.univ.filter
        (fun outcomes => Prod.map firstMap secondMap outcomes = (firstLabel, secondLabel)),
      heteroKron (firstMeas.effect outcomes.1) (secondMeas.effect outcomes.2)
  rw [heteroKron_finset_sum_left]
  simp_rw [heteroKron_finset_sum_right, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  by_cases hfirst : firstMap first = firstLabel <;> simp_all

private theorem postprocess_id {α I : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    (M : Measurement α I) : M.postprocess id = M := by
  apply Quantum.Measurement.ext
  intro a
  change (∑ b ∈ Finset.univ.filter (fun b => b = a), M.effect b) = M.effect a
  simp [Finset.filter_eq']

section

variable {α β γ I J : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Measurement α I) (N : Measurement β J)
include α β γ I J M N

/-- Postprocessing either readout of a tensor measurement is a relabeling of
its joint outcomes. -/
theorem tensorMeasurement_postprocess_left (f : α → γ) :
    tensorMeasurement (M.postprocess f) N =
      (tensorMeasurement M N).postprocess (Prod.map f id) := by
  simpa only [postprocess_id] using tensorMeasurement_postprocess M N f id

theorem tensorMeasurement_postprocess_right (f : β → γ) :
    tensorMeasurement M (N.postprocess f) =
      (tensorMeasurement M N).postprocess (Prod.map id f) := by
  simpa only [postprocess_id] using tensorMeasurement_postprocess M N id f

end

/-- Cauchy--Schwarz for a sum of vectors bounded by weighted scalars. -/
private theorem norm_sum_sq_le_weighted {X E : Type*} [SeminormedAddCommGroup E]
    (s : Finset X) (w r : X → ℝ) (v : X → E) (hw : ∀ x, 0 ≤ w x)
    (hv : ∀ x ∈ s, ‖v x‖ ≤ w x * r x) :
    ‖∑ x ∈ s, v x‖ ^ 2 ≤ (∑ x ∈ s, w x) * ∑ x ∈ s, w x * r x ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le_of_le s hv) 2).trans
    (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun x _ => hw x)
      (fun x _ => mul_nonneg (hw x) (sq_nonneg _)) (fun x _ => by rw [mul_pow, pow_two (w x), mul_assoc]))

/-- Averaging scalar contractions preserves state-dependent operator closeness
(`lem:avg-closeness`, paper `14_analysis_of_the_pauli_basis_test.tex:100-113`). -/
theorem avg_closeness {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (hμ : μ.IsProbability) (A B : X → Op ι)
    (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState
        (averageOperatorOverDistribution μ fun x => α x • (A x - B x)) ψ‖ ^ 2 ≤
      opDistSq μ A B ψ := by
  let v x := applyOperatorToState (A x - B x) ψ
  have h := norm_sum_sq_le_weighted μ.support μ.weight (fun x => ‖v x‖)
    (fun x => μ.weight x • (α x • v x)) μ.nonnegative (fun x _ => by
      rw [norm_smul_of_nonneg (μ.nonnegative x), norm_smul]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (hα _)) (μ.nonnegative _))
  rw [hμ.weight_sum_eq_one, one_mul] at h
  simpa [opDistSq, opFamilyDistSq, avgOver, averageOperatorOverDistribution, v,
    applyOperatorToState, ← Complex.coe_smul] using h

/-- Passing from answer-indexed POVM effects to unit-modulus weighted
observables costs at most the answer-alphabet cardinality (`lem:povm-to-obs`,
paper `14_analysis_of_the_pauli_basis_test.tex:115-129`). -/
theorem povm_to_obs_of_measurements {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ (fun x => ∑ a, c a • (A x).effect a)
        (fun x => ∑ a, c a • (B x).effect a) ψ ≤
      Fintype.card α * measurementDistSq μ A B ψ := by
  simp only [measurementDistSq, opDistSq, opFamilyDistSq, Fintype.sum_unique, ← avgOver_const_mul]
  refine avgOver_mono _ _ _ fun x => ?_
  let v a := applyOperatorToState ((A x).effect a - (B x).effect a) ψ
  have h := norm_sum_sq_le_weighted Finset.univ (fun _ => 1) (fun a => ‖v a‖)
    (fun a => c a • v a) (fun _ => zero_le_one) (fun a _ => by rw [norm_smul, hc a])
  simpa [v, applyOperatorToState, ← Finset.sum_sub_distrib, ← smul_sub] using h

end MIPStarRE.QPBT
