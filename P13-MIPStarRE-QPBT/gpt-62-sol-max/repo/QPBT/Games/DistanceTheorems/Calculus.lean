module

public import QPBT.Games.DistanceTheorems.TensorSupport
public import QPBT.Games.StrategyClasses
public import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core

/-!
# Consistency and state-dependent distance inequalities

This module collects the operator-level part of the state-dependent distance
calculus: the two-sided comparison between consistency defect and distance, the
monotonicity of the distance under products and function-indexed operators, its
triangle inequality and data-processing bound, and the approximate commutation
obtained from a joint projective refinement. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

## References

The source results run from blueprint `fact:agreement` through
`lem:commutation-analysis`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

section

variable {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
include X α ι μ A B ψ

/-- Consistency bounds state-dependent distance, with the explicit factor
hidden in blueprint `fact:agreement`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem opFamilyDistSq_le_two_mul_consistencyDefect :
    measurementDistSq μ A B ψ ≤
      2 * measurementDefect μ A
        B ψ := by
  unfold measurementDistSq measurementDefect opFamilyDistSq consistencyDefect
  rw [← avgOver_const_mul]
  exact avgOver_mono _ _ _ fun x => point_distance_le_two_defect (A x) (B x) ψ

/-- For projective POVMs, state-dependent distance bounds consistency. This is
the second item of blueprint `fact:agreement`,
paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem consistencyDefect_le_opFamilyDistSq_of_projective
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (hB : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x)) :
    measurementDefect μ A B ψ ≤
      measurementDistSq μ A B ψ := by
  have heq : measurementDistSq μ A B ψ = 2 * measurementDefect μ A B ψ := by
    unfold measurementDistSq measurementDefect opFamilyDistSq consistencyDefect
    rw [← avgOver_const_mul]
    exact avgOver_congr _ _ _ fun x =>
      point_distance_eq_two_defect_of_projective (A x) (B x) ψ (hA x) (hB x)
  linarith [opFamilyDistSq_nonneg μ (fun x => (A x).effect) (fun x => (B x).effect) ψ]

end

/-- Explicit squared-distance triangle inequality. This is blueprint
`fact:triangle`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:383-387`. -/
theorem opFamilyDistSq_le_of_le_of_le {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B C : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ ε : ℝ)
    (hAB : opFamilyDistSq μ A B ψ ≤ δ)
    (hBC : opFamilyDistSq μ B C ψ ≤ ε) :
    opFamilyDistSq μ A C ψ ≤ 2 * δ + 2 * ε := by
  have hpoint (x : X) (a : α) :
      ‖applyOperatorToState (A x a - C x a) ψ‖ ^ 2 ≤
        2 * ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 +
        2 * ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2 := by
    convert norm_add_sq_le_two (applyOperatorToState (A x a - B x a) ψ)
      (applyOperatorToState (B x a - C x a) ψ) using 1
    simp [← LinearMap.add_apply, ← map_add, applyOperatorToState]
  have h := avgOver_mono μ _ _ fun x => Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint x a)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, avgOver_add, avgOver_const_mul] at h
  unfold opFamilyDistSq at hAB hBC ⊢
  linarith only [h, hAB, hBC]

section ProductDistance

variable {X α β I : Type*} [Fintype α] [Fintype β] [Fintype I] [DecidableEq I]

/-- Multiplication by a measurement on the left contracts the distance, summing over
its outcome in addition to the original outcome. -/
theorem product_distance_mono (D : Distribution X) (M : X → Measurement α I)
    (U V : X → β → Op I) (ψ : EuclideanSpace ℂ I) :
    opFamilyDistSq D (fun x (ab : α × β) => (M x).effect ab.1 * U x ab.2)
      (fun x ab => (M x).effect ab.1 * V x ab.2) ψ ≤ opFamilyDistSq D U V ψ := by
  apply avgOver_mono
  intro x
  simp only [Fintype.sum_prod_type, ← mul_sub]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun b _ => sum_norm_mul_apply_le _ (U x b - V x b) ψ
    (measurement_sum_adjoint_mul_le_one (M x))

set_option maxHeartbeats 700000 in
/-- When the middle factors commute, the distance between two ordered products
is controlled by the distances between their respective factors. -/
theorem product_distance_le (D : Distribution X) (P A : X → Measurement α I)
    (Q B : X → Measurement β I) (ψ : EuclideanSpace ℂ I)
    (h : ∀ x a b, (P x).effect a * (B x).effect b = (B x).effect b * (P x).effect a) :
    opFamilyDistSq D (fun x (ab : α × β) => (P x).effect ab.1 * (Q x).effect ab.2)
      (fun x ab => (B x).effect ab.2 * (A x).effect ab.1) ψ ≤
      2 * measurementDistSq D Q B ψ +
      2 * measurementDistSq D P A ψ := by
  let d₁ := measurementDistSq D P A ψ
  let d₂ := measurementDistSq D Q B ψ
  change _ ≤ 2 * d₂ + 2 * d₁
  refine opFamilyDistSq_le_of_le_of_le D _
    (fun x (ab : α × β) => (P x).effect ab.1 * (B x).effect ab.2) _ ψ d₂ d₁ ?_ ?_
  · exact product_distance_mono D P (fun x b => (Q x).effect b) (fun x b => (B x).effect b) ψ
  · refine avgOver_mono _ _ _ fun x => ?_
    simp only [Fintype.sum_prod_type, h, ← mul_sub]
    exact Finset.sum_le_sum fun a _ => sum_norm_mul_apply_le _ _ ψ
      (measurement_sum_adjoint_mul_le_one (B x))

end ProductDistance

/-- Triangle inequality for consistency on a unit state under a probability
distribution, with the square-root loss of blueprint
`fact:triangle-for-simeq`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-395`. -/
theorem consistencyDefect_trans_le {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B C D : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (ε δ γ : ℝ)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hAB : measurementDefect μ A
      B ψ ≤ ε)
    (hCB : measurementDefect μ C
      B ψ ≤ δ)
    (hCD : measurementDefect μ C
      D ψ ≤ γ) :
    measurementDefect μ A
      D ψ ≤ ε + 2 * Real.sqrt (δ + γ) := by
  have hCBdist := (opFamilyDistSq_le_two_mul_consistencyDefect μ C B ψ).trans
    (mul_le_mul_of_nonneg_left hCB (by norm_num))
  have hCDdist := (opFamilyDistSq_le_two_mul_consistencyDefect μ C D ψ).trans
    (mul_le_mul_of_nonneg_left hCD (by norm_num))
  have hBDdist := opFamilyDistSq_le_of_le_of_le μ
    (fun x => (B x).effect) (fun x => (C x).effect) (fun x => (D x).effect) ψ _ _
    (by simpa only [opFamilyDistSq_symm μ (fun x => (B x).effect)] using hCBdist) hCDdist
  rw [show 2 * (2 * δ) + 2 * (2 * γ) = 4 * (δ + γ) by ring] at hBDdist
  have hgap := le_of_abs_le (abs_overlap_gap_le_sqrt_of_opFamilyDistSq μ A _ _ ψ hμ hψ _ hBDdist)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num] at hgap
  rw [consistencyDefect_eq_one_sub_overlap μ A B ψ hμ hψ] at hAB
  rw [consistencyDefect_eq_one_sub_overlap μ A D ψ hμ hψ]
  linarith only [hAB, hgap]

section

variable {X α β ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA)
    (B : X → Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
include X α β ιA ιB μ A B ψ

/-- Coarse-graining measurements on opposite tensor factors cannot increase
inconsistency. This is blueprint
`fact:data-processing`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-401`. -/
theorem consistencyDefect_postprocess_question_le
    (f : X → α → β) :
    bipartiteDefect μ
        (fun x => (A x).postprocess (f x))
        (fun x => (B x).postprocess (f x)) ψ ≤
      bipartiteDefect μ A
        B ψ := by
  change measurementDefect μ (fun x => leftPlacedMeasurement ((A x).postprocess (f x)))
      (fun x => rightPlacedMeasurement ((B x).postprocess (f x))) ψ ≤
    measurementDefect μ (fun x => leftPlacedMeasurement (A x)) (fun x => rightPlacedMeasurement (B x)) ψ
  unfold measurementDefect consistencyDefect
  refine avgOver_mono _ _ _ fun x => ?_
  simp only [point_defect_eq]
  simp only [leftPlacedMeasurement_effect, rightPlacedMeasurement_effect, placed_product_stateQForm_eq]
  exact sub_le_sub_left (diagonal_postprocess_stateQForm_ge ψ (A x) (B x) (f x)) _

theorem consistencyDefect_postprocess_le
    (f : α → β) :
    bipartiteDefect μ
        (fun x => (A x).postprocess f)
        (fun x => (B x).postprocess f) ψ ≤
      bipartiteDefect μ A
        B ψ :=
  consistencyDefect_postprocess_question_le μ A B ψ (fun _ => f)

end

/-- Joint closeness to a projective refinement implies approximate
commutation. The bound has one universal constant, independent of the finite
alphabets, Hilbert space, distributions, operators, state, and error; blueprint
`lem:commutation-analysis`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:410-461`. -/
theorem op_dist_sq_commutator_le_explicit
    {X α β ιA ιB : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (D : X → Measurement β ιA)
    (B : X → Measurement (α × β) ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) {δ : ℝ}
    (a : α) (b : β)
    (hB : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x))
    (hAB : opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 (((B x).postprocess Prod.fst).effect a)) ψ ≤ δ)
    (hDB : opFamilyDistSq μ (fun x b => heteroKron ((D x).effect b) 1)
      (fun x b => heteroKron 1 (((B x).postprocess Prod.snd).effect b)) ψ ≤ δ) :
    avgOver μ (fun x => ‖applyOperatorToState
      (heteroKron ((A x).effect a * (D x).effect b - (D x).effect b * (A x).effect a) 1) ψ‖ ^ 2) ≤
      16 * δ := by
  let L₁ x := leftPlacedMeasurement (ιB := ιB) (A x)
  let L₂ x := leftPlacedMeasurement (ιB := ιB) (D x)
  let R₁ x := rightPlacedMeasurement (ιA := ιA) ((B x).postprocess Prod.fst)
  let R₂ x := rightPlacedMeasurement (ιA := ιA) ((B x).postprocess Prod.snd)
  let J x ab := rightTensor (ι₁ := ιA) ((B x).effect ab)
  let F x (ab : α × β) := (L₁ x).effect ab.1 * (L₂ x).effect ab.2
  let G x (ab : α × β) := (L₂ x).effect ab.2 * (L₁ x).effect ab.1
  have h₁ : opFamilyDistSq μ F J ψ ≤ 4 * δ := by
    have h := product_distance_le μ L₁ R₁ L₂ R₂ ψ (fun _ _ _ => left_right_commute _ _)
    simp only [R₁, R₂, rightPlacedMeasurement_effect, heteroKron_mul, mul_one,
      joint_marginal_product_rev _ (hB _)] at h
    change opFamilyDistSq μ F J ψ ≤ _ at h
    refine h.trans ?_
    simp only [measurementDistSq, L₁, L₂, leftPlacedMeasurement_effect, rightPlacedMeasurement_effect]
    linarith only [hAB, hDB]
  have h₂ : opFamilyDistSq μ G J ψ ≤ 4 * δ := by
    rw [opFamilyDistSq_reindex μ (Equiv.prodComm α β)]
    have h := product_distance_le μ L₂ R₂ L₁ R₁ ψ (fun _ _ _ => left_right_commute _ _)
    simp only [R₁, R₂, rightPlacedMeasurement_effect, heteroKron_mul, mul_one,
      joint_marginal_product _ (hB _)] at h
    refine h.trans ?_
    simp only [measurementDistSq, L₁, L₂, leftPlacedMeasurement_effect, rightPlacedMeasurement_effect]
    linarith only [hAB, hDB]
  have hFG : opFamilyDistSq μ F G ψ ≤ 16 * δ := by
    rw [opFamilyDistSq_symm] at h₂
    linarith only [opFamilyDistSq_le_of_le_of_le μ F J G ψ _ _ h₁ h₂]
  refine (avgOver_mono μ _ _ ?_).trans hFG
  intro x
  simpa only [F, G, L₁, L₂, leftPlacedMeasurement_effect, heteroKron_mul,
    mul_one, ← heteroKron_sub_left] using
      Finset.single_le_sum (f := fun p => ‖applyOperatorToState (F x p - G x p) ψ‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ (a, b))

end MIPStarRE.QPBT
