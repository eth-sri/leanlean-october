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

variable {X α ι : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] (μ : Distribution X)

/-- Consistency bounds state-dependent distance, with the explicit factor
hidden in blueprint `fact:agreement`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem opFamilyDistSq_le_two_mul_consistencyDefect (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      2 * consistencyDefect μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ := by
  unfold opFamilyDistSq consistencyDefect avgOver
  calc
    (∑ x ∈ μ.support, μ.weight x *
        ∑ a : α, ‖applyOperatorToState ((A x).effect a - (B x).effect a) ψ‖ ^ 2) ≤
      ∑ x ∈ μ.support, μ.weight x *
        (2 * ∑ a : α, ∑ b : α, if a = b then 0 else
          stateQForm ψ ((A x).effect a * (B x).effect b)) := by
      refine Finset.sum_le_sum ?_
      intro x _
      exact mul_le_mul_of_nonneg_left
        (point_distance_le_two_defect (A x) (B x) ψ) (μ.nonnegative x)
    _ = 2 * ∑ x ∈ μ.support, μ.weight x *
        (∑ a : α, ∑ b : α, if a = b then 0 else
          stateQForm ψ ((A x).effect a * (B x).effect b)) := by
      rw [Finset.mul_sum]
      grind

/-- Consistency bounds the state-dependent distance of two oppositely placed
measurement families. This is the first item of `fact:agreement`, blueprint
`ch12_qpbt_games.tex:260-276`, in the placed form used by the trailing clause
of `lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:699-701`,
paper `14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_two_mul_consistencyDefect {ιA ιB : Type*} [Fintype ιA]
    [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤
      2 * consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ :=
  opFamilyDistSq_le_two_mul_consistencyDefect μ
    (fun x => leftPlacedMeasurement (A x)) (fun x => rightPlacedMeasurement (B x)) ψ

/-- Consistency at level `c` gives operator distance at level `2 * c` for two
oppositely placed measurement families, blueprint `ch12_qpbt_games.tex:260-276`. -/
theorem opFamilyDistSq_placed_le_of_consistencyDefect_le {ιA ιB : Type*} [Fintype ιA]
    [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) {c : ℝ}
    (h : consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ c) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 2 * c :=
  (opFamilyDistSq_placed_le_two_mul_consistencyDefect μ A B ψ).trans (by linarith)

/-- For projective POVMs, state-dependent distance bounds consistency. This is
the second item of blueprint `fact:agreement`,
paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem consistencyDefect_le_opFamilyDistSq_of_projective (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (hB : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x)) :
    consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      opFamilyDistSq μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ := by
  have heq :
      opFamilyDistSq μ (fun x a => (A x).effect a)
          (fun x a => (B x).effect a) ψ =
        2 * consistencyDefect μ (fun x a => (A x).effect a)
          (fun x a => (B x).effect a) ψ := by
    unfold opFamilyDistSq consistencyDefect avgOver
    simp_rw [consistency_term_eq_stateQForm]
    calc
      (∑ x ∈ μ.support, μ.weight x *
          ∑ a : α,
            ‖applyOperatorToState ((A x).effect a - (B x).effect a) ψ‖ ^ 2) =
        ∑ x ∈ μ.support, μ.weight x *
          (2 * ∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ ((A x).effect a * (B x).effect b)) := by
        simp_all [point_distance_eq_two_defect_of_projective]
      _ = 2 * ∑ x ∈ μ.support, μ.weight x *
          (∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ ((A x).effect a * (B x).effect b)) := by
        rw [Finset.mul_sum]
        grind
  grind [opFamilyDistSq_nonneg]

/-- Left multiplication by a square-summable operator family does not increase
state-dependent distance. This is blueprint
`fact:add-a-proj`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:313-344`. -/
theorem opFamilyDistSq_mul_left_le {X Y α β γ ι : Type*}
    [DecidableEq X] [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution (X × Y)) (A B : X → (α × β) → Op ι)
    (C : Y → α → γ → Op ι) (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hC : ∀ y a, (1 - ∑ c : γ, (C y a c)ᴴ * C y a c).PosSemidef)
    (h : opFamilyDistSq (μ.map Prod.fst) A B ψ ≤ δ) :
    opFamilyDistSq μ
      (fun p (abc : (α × β) × γ) =>
        C p.2 abc.1.1 abc.2 * A p.1 (abc.1.1, abc.1.2))
      (fun p (abc : (α × β) × γ) =>
        C p.2 abc.1.1 abc.2 * B p.1 (abc.1.1, abc.1.2)) ψ ≤ δ := by
  have hC' (y : Y) (a : α) :
      ∑ c : γ, (C y a c)ᴴ * C y a c ≤ 1 :=
    Matrix.le_iff.mpr (hC y a)
  calc
    opFamilyDistSq μ
        (fun p (abc : (α × β) × γ) =>
          C p.2 abc.1.1 abc.2 * A p.1 (abc.1.1, abc.1.2))
        (fun p (abc : (α × β) × γ) =>
          C p.2 abc.1.1 abc.2 * B p.1 (abc.1.1, abc.1.2)) ψ
        ≤ opFamilyDistSq μ (fun p ab => A p.1 ab) (fun p ab => B p.1 ab) ψ := by
          apply avgOver_mono
          intro p
          rw [Fintype.sum_prod_type]
          apply Finset.sum_le_sum
          intro ab _
          simpa only [mul_sub] using
            sum_norm_mul_apply_le (fun c => C p.2 ab.1 c)
              (A p.1 ab - B p.1 ab) ψ (hC' p.2 ab.1)
    _ = opFamilyDistSq (μ.map Prod.fst) A B ψ := by
      simp [opFamilyDistSq, Distribution.avgOver_map, applyOperatorToState, symm]
    _ ≤ δ := h

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
  have hpoint : ∀ x a,
      ‖applyOperatorToState (A x a - C x a) ψ‖ ^ 2 ≤
        2 * ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 +
          2 * ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2 := by
    intro x a
    have hdecomp : applyOperatorToState (A x a - C x a) ψ =
        applyOperatorToState (A x a - B x a) ψ +
          applyOperatorToState (B x a - C x a) ψ := by
      simp [applyOperatorToState]
    rw [hdecomp]
    let u := applyOperatorToState (A x a - B x a) ψ
    let v := applyOperatorToState (B x a - C x a) ψ
    calc
      ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (norm_add_le u v)
      _ ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
        nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  calc
    avgOver μ (fun x => ∑ a, ‖applyOperatorToState (A x a - C x a) ψ‖ ^ 2)
        ≤ avgOver μ (fun x => ∑ a,
          (2 * ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2 +
            2 * ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2)) := by
          simp_all [avgOver_mono, Finset.sum_le_sum]
    _ = 2 * avgOver μ (fun x => ∑ a,
          ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2) +
        2 * avgOver μ (fun x => ∑ a,
          ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [avgOver_add, avgOver_const_mul]
    _ ≤ 2 * δ + 2 * ε := add_le_add
      (mul_le_mul_of_nonneg_left hAB (by positivity))
      (mul_le_mul_of_nonneg_left hBC (by positivity))

/-- Triangle inequality for consistency on a unit state under a probability
distribution, with the square-root loss of blueprint
`fact:triangle-for-simeq`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-395`. -/
theorem consistencyDefect_trans_le (A B C D : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (ε δ γ : ℝ)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hAB : consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ ≤ ε)
    (hCB : consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (B x).effect a) ψ ≤ δ)
    (hCD : consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ ≤ γ) :
    consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (D x).effect a) ψ ≤ ε + 2 * Real.sqrt (δ + γ) := by
  letI : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have hzero : ψ = 0 := Subsingleton.elim _ _
    simp_all
  have hCBdist : opFamilyDistSq μ (fun x a => (C x).effect a)
      (fun x a => (B x).effect a) ψ ≤ 2 * δ := by
    calc
      _ ≤ 2 * consistencyDefect μ (fun x a => (C x).effect a)
          (fun x a => (B x).effect a) ψ :=
        opFamilyDistSq_le_two_mul_consistencyDefect μ C B ψ
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hCB (by norm_num)
  have hBCdist : opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (C x).effect a) ψ ≤ 2 * δ := by
    rw [opFamilyDistSq_symm]
    exact hCBdist
  have hCDdist : opFamilyDistSq μ (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ ≤ 2 * γ := by
    calc
      _ ≤ 2 * consistencyDefect μ (fun x a => (C x).effect a)
          (fun x a => (D x).effect a) ψ :=
        opFamilyDistSq_le_two_mul_consistencyDefect μ C D ψ
      _ ≤ 2 * γ := mul_le_mul_of_nonneg_left hCD (by norm_num)
  have hBDdist : opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (D x).effect a) ψ ≤ 4 * (δ + γ) := by
    have htri := opFamilyDistSq_le_of_le_of_le μ
      (fun x a => (B x).effect a) (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ (2 * δ) (2 * γ) hBCdist hCDdist
    linarith
  have hgap := overlap_gap_le_of_opFamilyDistSq μ A B D ψ hμ hψ
    (4 * (δ + γ)) hBDdist
  have hsqrt : Real.sqrt (4 * (δ + γ)) = 2 * Real.sqrt (δ + γ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [consistencyDefect_eq_one_sub_overlap μ A B ψ hμ hψ] at hAB
  rw [consistencyDefect_eq_one_sub_overlap μ A D ψ hμ hψ]
  grind

/-- Coarse-graining measurements on opposite tensor factors cannot increase
inconsistency. This is blueprint
`fact:data-processing`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-401`. -/
theorem consistencyDefect_postprocess_le {X α β ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA)
    (B : X → Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (f : α → β) :
    consistencyDefect μ
        (fun x b => heteroKron (((A x).postprocess f).effect b) 1)
        (fun x b => heteroKron 1 (((B x).postprocess f).effect b)) ψ ≤
      consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm]
  apply avgOver_mono
  intro x
  rw [show (∑ b : β, ∑ c : β, if b = c then 0 else
      stateQForm ψ
        (heteroKron (((A x).postprocess f).effect b) 1 *
          heteroKron 1 (((B x).postprocess f).effect c))) =
      ‖ψ‖ ^ 2 - ∑ b : β, stateQForm ψ
        (heteroKron (((A x).postprocess f).effect b)
          (((B x).postprocess f).effect b)) by
    simpa [leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne,
      placed_product_stateQForm_eq] using
      point_defect_eq
        (leftPlacedMeasurement ((A x).postprocess f))
        (rightPlacedMeasurement ((B x).postprocess f)) ψ]
  rw [show (∑ a : α, ∑ a' : α, if a = a' then 0 else
      stateQForm ψ
        (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a'))) =
      ‖ψ‖ ^ 2 - ∑ a : α,
        stateQForm ψ (heteroKron ((A x).effect a) ((B x).effect a)) by
    simpa [leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne,
      placed_product_stateQForm_eq] using
      point_defect_eq (leftPlacedMeasurement (A x))
        (rightPlacedMeasurement (B x)) ψ]
  exact sub_le_sub_left (diagonal_postprocess_stateQForm_ge ψ (A x) (B x) f) _

/-- Formalization-only same-question specialization of
`opFamilyDistSq_mul_left_le`, obtained by pushing the question distribution
along the diagonal map. -/
theorem opFamilyDistSq_mul_left_same_question_le {X α β γ ι : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → (α × β) → Op ι)
    (C : X → α → γ → Op ι) (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hC : ∀ x a, (1 - ∑ c : γ, (C x a c)ᴴ * C x a c).PosSemidef)
    (h : opFamilyDistSq μ A B ψ ≤ δ) :
    opFamilyDistSq μ
      (fun x (abc : (α × β) × γ) =>
        C x abc.1.1 abc.2 * A x (abc.1.1, abc.1.2))
      (fun x (abc : (α × β) × γ) =>
        C x abc.1.1 abc.2 * B x (abc.1.1, abc.1.2)) ψ ≤ δ := by
  classical
  let μdiag : Distribution (X × X) := μ.map (fun x => (x, x))
  have hbase : opFamilyDistSq (μdiag.map Prod.fst) A B ψ ≤ δ := by
    simpa [μdiag, opFamilyDistSq, Distribution.avgOver_map] using h
  have hout := opFamilyDistSq_mul_left_le μdiag A B C ψ δ hC hbase
  grind [opFamilyDistSq, Distribution.avgOver_map]

theorem opFamilyDistSq_commutator_le_of_close {X α β γ ι : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A BA : X → α × β → Op ι) (D BD : X → α × γ → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hA : ∀ x a, (1 - ∑ b, (A x (a, b))ᴴ * A x (a, b)).PosSemidef)
    (hD : ∀ x a, (1 - ∑ c, (D x (a, c))ᴴ * D x (a, c)).PosSemidef)
    (hBA : ∀ x a, (1 - ∑ b, (BA x (a, b))ᴴ * BA x (a, b)).PosSemidef)
    (hBD : ∀ x a, (1 - ∑ c, (BD x (a, c))ᴴ * BD x (a, c)).PosSemidef)
    (hcA : ∀ x (abc : (α × β) × γ),
      BD x (abc.1.1, abc.2) * A x abc.1 = A x abc.1 * BD x (abc.1.1, abc.2))
    (hcD : ∀ x (abc : (α × β) × γ),
      BA x abc.1 * D x (abc.1.1, abc.2) = D x (abc.1.1, abc.2) * BA x abc.1)
    (hJ : ∀ x (abc : (α × β) × γ),
      BD x (abc.1.1, abc.2) * BA x abc.1 = BA x abc.1 * BD x (abc.1.1, abc.2))
    (h₁ : opFamilyDistSq μ A BA ψ ≤ δ) (h₂ : opFamilyDistSq μ D BD ψ ≤ δ) :
    opFamilyDistSq μ (fun x (abc : (α × β) × γ) => A x abc.1 * D x (abc.1.1, abc.2))
      (fun x abc => D x (abc.1.1, abc.2) * A x abc.1) ψ ≤ 16 * δ := by
  have h1 := opFamilyDistSq_mul_left_same_question_le μ D BD (fun x a b => A x (a, b)) ψ δ hA h₂
  have h2 := opFamilyDistSq_mul_left_same_question_le μ A BA (fun x a c => BD x (a, c)) ψ δ hBD h₁
  have h3 := opFamilyDistSq_mul_left_same_question_le μ A BA (fun x a c => D x (a, c)) ψ δ hD h₁
  have h4 := opFamilyDistSq_mul_left_same_question_le μ D BD (fun x a b => BA x (a, b)) ψ δ hBA h₂
  rw [opFamilyDistSq_reindex μ (swapLast α β γ)] at h1 h4
  simp only [swapLast_symm_apply, Prod.mk.eta, hcA, hcD, hJ] at h1 h2 h3 h4
  have h5 := opFamilyDistSq_le_of_le_of_le μ _ _ _ ψ _ _ h3 h4
  rw [opFamilyDistSq_symm] at h5
  exact (opFamilyDistSq_le_of_le_of_le μ _ _ _ ψ _ _
    (opFamilyDistSq_le_of_le_of_le μ _ _ _ ψ _ _ h1 h2) h5).trans (by linarith)

/-- Joint closeness to a projective refinement implies approximate
commutation. The bound has one universal constant, independent of the finite
alphabets, Hilbert space, distributions, operators, state, and error; blueprint
`lem:commutation-analysis`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:410-461`. -/
theorem op_dist_sq_commutator_le_explicit :
    ∀ {X α β γ ιA ιB : Type*}
      [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
      [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
      (μ : Distribution X)
      (A : X → Measurement (α × β) ιA)
      (B : X → Measurement ((α × β) × γ) ιB)
      (D : X → Measurement (α × γ) ιA)
      (ψ : EuclideanSpace ℂ (ιA × ιB)) (δ : ℝ),
      (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x)) →
      opFamilyDistSq μ
        (fun x ab => heteroKron ((A x).effect ab) 1)
        (fun x ab => heteroKron 1 (((B x).postprocess
          (fun abc => abc.1)).effect ab)) ψ ≤ δ →
      opFamilyDistSq μ
        (fun x ac => heteroKron ((D x).effect ac) 1)
        (fun x ac => heteroKron 1 (((B x).postprocess
          (fun abc => (abc.1.1, abc.2))).effect ac)) ψ ≤ δ →
      opFamilyDistSq μ
        (fun x (abc : (α × β) × γ) => heteroKron
          (((A x).effect (abc.1.1, abc.1.2)) * ((D x).effect (abc.1.1, abc.2)) -
            ((D x).effect (abc.1.1, abc.2)) * ((A x).effect (abc.1.1, abc.1.2))) 1)
        (fun _ _ => 0) ψ ≤ 16 * δ := by
  intro X α β γ ιA ιB _ _ _ _ _ _ _ _ _ _ μ A B D ψ δ hB hAB hDB
  have := opFamilyDistSq_commutator_le_of_close μ (fun x ab => heteroKron ((A x).effect ab) 1)
    (fun x ab => heteroKron 1 (((B x).postprocess (fun abc => abc.1)).effect ab))
    (fun x ac => heteroKron ((D x).effect ac) 1)
    (fun x ac => heteroKron 1 (((B x).postprocess (fun abc => (abc.1.1, abc.2))).effect ac)) ψ δ
    (fun x a => left_fiber_contraction (A x) a) (fun x a => left_fiber_contraction (D x) a)
    (fun x a => right_fiber_contraction _ a) (fun x a => right_fiber_contraction _ a)
    (fun x abc => (left_right_commute _ _).symm) (fun x abc => (left_right_commute _ _).symm)
    (fun x abc => by rw [heteroKron_mul, heteroKron_mul,
      (postprocess_effect_commute _ (hB x) _ _ _ _).eq]) hAB hDB
  refine le_of_eq_of_le (opFamilyDistSq_congr_sub μ _ _ _ _ ψ fun x abc => ?_) this
  simp [heteroKron_mul, heteroKron_sub_left]


end MIPStarRE.QPBT
