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

/-- The product POVM whose effects are Kronecker products of the two factor effects. -/
noncomputable def tensorMeasurement
    {α β I J : Type*} [Fintype α] [Fintype β]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement α I) (B : Measurement β J) :
    Measurement (α × β) (I × J) :=
  Measurement.ofSumEqOne
    (fun ab => heteroKron (A.effect ab.1) (B.effect ab.2))
    (fun ab => MIPStarRE.Quantum.kronecker_nonneg (A.pos ab.1) (B.pos ab.2))
    (by
      change ∑ ab : α × β, opTensor (A.effect ab.1) (B.effect ab.2) = 1
      rw [Fintype.sum_prod_type]
      calc
        (∑ a : α, ∑ b : β, opTensor (A.effect a) (B.effect b)) =
            ∑ a : α, leftTensor (A.effect a) *
              (∑ b : β, rightTensor (B.effect b)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Matrix.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          exact (leftTensor_mul_rightTensor_eq_opTensor _ _).symm
        _ = 1 := by
          rw [rightTensor_finset_sum, B.sum_eq_one, rightTensor_one]
          simp_rw [Matrix.mul_one]
          rw [leftTensor_finset_sum, A.sum_eq_one, leftTensor_one])

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
  by_cases hfirst : firstMap first = firstLabel <;> simp [hfirst]

/-- The squared effects of a POVM sum to at most the identity. This is the
formalization-only estimate `lem:sandwich-povm-square-sum` used in the
contractions underlying `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_sum_adjoint_mul_le_one
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    (M : Measurement α I) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  calc
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ ∑ a : α, M.effect a := by
      apply Finset.sum_le_sum
      intro a _
      rw [measurement_effect_hermitian]
      exact MIPStarRE.Quantum.sq_le_self (M.pos a) (measurement_effect_le_one M a)
    _ = 1 := M.sum_eq_one

/-- Averaging contractions preserves state-dependent operator closeness.
This is blueprint
`lem:avg-closeness`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:100-113`.
The probability hypothesis is explicit because the proof uses Jensen's
inequality for the average. -/
theorem avg_closeness {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (hμ : μ.IsProbability) (A B : X → Op ι)
    (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState
        (averageOperatorOverDistribution μ fun x =>
          α x • (A x - B x)) ψ‖ ^ 2 ≤
      opDistSq μ A B ψ := by
  let v : X → EuclideanSpace ℂ ι :=
    fun x => applyOperatorToState (A x - B x) ψ
  have happly :
      applyOperatorToState
          (averageOperatorOverDistribution μ fun x => α x • (A x - B x)) ψ =
        ∑ x ∈ μ.support, μ.weight x • (α x • v x) := by
    unfold averageOperatorOverDistribution applyOperatorToState
    rw [map_sum]
    simp only [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [← smul_assoc, map_smul]
    simp only [v, applyOperatorToState, Complex.real_smul, map_sub,
      LinearMap.smul_apply, LinearMap.sub_apply]
    rw [← smul_assoc, Complex.real_smul]
  have hnorm :
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
        ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := by
    calc
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
          ∑ x ∈ μ.support, ‖μ.weight x • (α x • v x)‖ :=
        norm_sum_le μ.support _
      _ ≤ ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_smul_of_nonneg (μ.nonnegative x), norm_smul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [one_mul] using
            mul_le_of_le_one_left (norm_nonneg (v x)) (hα x))
          (μ.nonnegative x)
  have hrhs_nonneg :
      0 ≤ ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x) (sq_nonneg _)
  have havg_norm :
      |avgOver μ (fun x => ‖v x‖)| ≤
        Real.sqrt (avgOver μ (fun x => ‖v x‖ ^ 2)) := by
    exact MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ
      (fun x => ‖v x‖) (fun x => ‖v x‖ ^ 2)
      (fun x => by rw [abs_norm, Real.sqrt_sq_eq_abs, abs_norm])
      (fun x => sq_nonneg ‖v x‖) (by rw [hμ.weight_sum_eq_one])
  have hnorm_sqrt :
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
        Real.sqrt (∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2) := by
    calc
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
          ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := hnorm
      _ ≤ |avgOver μ (fun x => ‖v x‖)| := le_abs_self _
      _ ≤ Real.sqrt (avgOver μ (fun x => ‖v x‖ ^ 2)) := havg_norm
  rw [happly]
  unfold opDistSq opFamilyDistSq avgOver
  simp only [Fintype.sum_unique]
  change ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ^ 2 ≤
    ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2
  calc
    ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ^ 2 ≤
        (Real.sqrt (∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm_sqrt
    _ = ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2 :=
      Real.sq_sqrt hrhs_nonneg

/-- Formalization-only auxiliary for `lem:povm-to-obs`: passing from arbitrary
answer-indexed operator families to unit-modulus weighted sums costs at most the
answer-alphabet cardinality. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:115-129` states
the specialization to POVMs. -/
theorem povm_to_obs {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ (fun x => ∑ a, c a • A x a) (fun x => ∑ a, c a • B x a) ψ ≤
      Fintype.card α * opFamilyDistSq μ A B ψ := by
  have hpoint : ∀ x,
      ‖applyOperatorToState
          ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ‖ ^ 2 ≤
        (Fintype.card α : ℝ) *
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 := by
    intro x
    have hrewrite :
        applyOperatorToState
            ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ =
          ∑ a, c a • applyOperatorToState (A x a - B x a) ψ := by
      simp [applyOperatorToState, ← Finset.sum_sub_distrib, ← smul_sub]
    rw [hrewrite]
    have hnorm :
        ‖∑ a, c a • applyOperatorToState (A x a - B x a) ψ‖ ≤
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ := by
      calc
        ‖∑ a, c a • applyOperatorToState (A x a - B x a) ψ‖ ≤
            ∑ a, ‖c a • applyOperatorToState (A x a - B x a) ψ‖ :=
          norm_sum_le Finset.univ _
        _ = ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ := by
          apply Finset.sum_congr rfl
          intro a _
          simp [norm_smul, hc a]
    calc
      ‖∑ a, c a • applyOperatorToState (A x a - B x a) ψ‖ ^ 2 ≤
          (∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 hnorm
      _ ≤ (Fintype.card α : ℝ) *
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ)
          (f := fun a : α => ‖applyOperatorToState (A x a - B x a) ψ‖))
  unfold opDistSq opFamilyDistSq
  simp only [Fintype.sum_unique]
  calc
    avgOver μ (fun x =>
        ‖applyOperatorToState
          ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ‖ ^ 2) ≤
      avgOver μ (fun x =>
        (Fintype.card α : ℝ) *
          ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2) :=
      avgOver_mono μ _ _ hpoint
    _ = (Fintype.card α : ℝ) * avgOver μ (fun x =>
        ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2) :=
      avgOver_const_mul _ _ _

/-- Passing from answer-indexed POVM effects to unit-modulus weighted
observables costs at most the answer-alphabet cardinality. This is
blueprint
`lem:povm-to-obs`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:115-129`. -/
theorem povm_to_obs_of_measurements {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ (fun x => ∑ a, c a • (A x).effect a)
        (fun x => ∑ a, c a • (B x).effect a) ψ ≤
      Fintype.card α * opFamilyDistSq μ
        (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ := by
  exact povm_to_obs μ (fun x a => (A x).effect a)
    (fun x a => (B x).effect a) c hc ψ

end MIPStarRE.QPBT
