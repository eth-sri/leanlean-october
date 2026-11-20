module

public import QPBT.Games.StateTransport
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

variable {X α ι : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype ι]
  [DecidableEq ι] (μ : Distribution X) (A B : X → Measurement α ι) (ψ : EuclideanSpace ℂ ι)

/-- Consistency bounds state-dependent distance, with the explicit factor
hidden in blueprint `fact:agreement`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem opFamilyDistSq_le_two_mul_consistencyDefect :
    opFamilyDistSq μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      2 * consistencyDefect μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ := by
  unfold opFamilyDistSq consistencyDefect avgOver
  simp_rw [consistency_term_eq_stateQForm]
  calc
    _ ≤
      ∑ x ∈ μ.support, μ.weight x *
        (2 * ∑ a : α, ∑ b : α, if a = b then 0 else
          stateQForm ψ ((A x).effect a * (B x).effect b)) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (point_distance_le_two_defect (A x) (B x) ψ) (μ.nonnegative x)
    _ = _ := by
      rw [Finset.mul_sum]
      congr 1 with x
      ring

/-- For projective POVMs, state-dependent distance bounds consistency. This is
the second item of blueprint `fact:agreement`,
paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem consistencyDefect_le_opFamilyDistSq_of_projective
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (hB : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x)) :
    consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      opFamilyDistSq μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ := by
  have heq :
      opFamilyDistSq μ (fun x => (A x).effect)
          (fun x => (B x).effect) ψ =
        2 * consistencyDefect μ (fun x => (A x).effect)
          (fun x => (B x).effect) ψ := by
    unfold opFamilyDistSq consistencyDefect avgOver
    simp_rw [consistency_term_eq_stateQForm]
    calc
      _ =
        _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [point_distance_eq_two_defect_of_projective
          _ _ ψ (hA x) (hB x)]
      _ = _ := by
        rw [Finset.mul_sum]
        congr 1 with x
        ring
  grind [opFamilyDistSq_nonneg]

end

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
  have hC' (y : Y) (a : α)  :=
    Matrix.le_iff.mpr (hC y a)
  calc
    _
        ≤ opFamilyDistSq μ (fun p => A p.1) (fun p => B p.1) ψ := by
          apply avgOver_mono
          intro p
          rw [Fintype.sum_prod_type]
          apply Finset.sum_le_sum
          intro ab _
          simpa only [mul_sub] using
            sum_norm_mul_apply_le _
              (A p.1 ab - B p.1 ab) ψ (hC' p.2 ab.1)
    _ = opFamilyDistSq (μ.map Prod.fst) A B ψ := Eq.symm (Distribution.avgOver_map μ Prod.fst fun x => ∑ a, ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2)
    _ ≤ δ := h

/-- Explicit squared-distance triangle inequality. This is blueprint
`fact:triangle`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:383-387`. -/
theorem opFamilyDistSq_le_of_le_of_le {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    {μ : Distribution X} (A B C : X → α → Op ι)
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
      _ ≤ _ :=
        (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (norm_add_le u v)
      _ ≤ _ := by
        nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  calc
    _
        ≤ _ := by
          apply avgOver_mono
          solve_by_elim [Finset.sum_le_sum]
    _ = 2 * avgOver μ (fun x => ∑ a,
          ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2) +
        2 * avgOver μ (fun x => ∑ a,
          ‖applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [avgOver_add, avgOver_const_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hAB (by positivity))
      (mul_le_mul_of_nonneg_left hBC (by positivity))

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
    (hAB : consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ ≤ ε)
    (hCB : consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (B x).effect a) ψ ≤ δ)
    (hCD : consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ ≤ γ) :
    consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (D x).effect a) ψ ≤ ε + 2 * Real.sqrt (δ + γ) := by
  have hBCdist : opFamilyDistSq μ (fun x => (B x).effect)
      (fun x => (C x).effect) ψ ≤ 2 * δ := by
    rw [opFamilyDistSq_symm]
    calc
      _ ≤ _ :=
        opFamilyDistSq_le_two_mul_consistencyDefect μ C B ψ
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hCB (by norm_num)
  have hCDdist : opFamilyDistSq μ (fun x => (C x).effect)
      (fun x => (D x).effect) ψ ≤ 2 * γ := by
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect μ C D ψ) ?_
    gcongr
  have hBDdist : opFamilyDistSq μ (fun x => (B x).effect)
      (fun x => (D x).effect) ψ ≤ 4 * (δ + γ) := by
    have htri := opFamilyDistSq_le_of_le_of_le
      _ _
      _ ψ _ _ hBCdist hCDdist
    linarith
  have hgap := abs_overlap_gap_le_sqrt_of_opFamilyDistSq μ A _ _ ψ hμ hψ hBDdist
  have hsqrt : Real.sqrt (4 * (δ + γ)) = 2 * Real.sqrt (δ + γ) := by
    norm_num
  rw [consistencyDefect_eq_one_sub_overlap A B hμ hψ] at hAB
  rw [consistencyDefect_eq_one_sub_overlap A D hμ hψ]
  have hdiff :
      avgOver μ (fun x => ∑ a,
          stateQForm ψ ((A x).effect a * (B x).effect a)) -
        avgOver μ (fun x => ∑ a,
          stateQForm ψ ((A x).effect a * (D x).effect a)) ≤
        2 * Real.sqrt (δ + γ) := by
    calc
      _ ≤ _ := le_abs_self _
      _ ≤ _ := hgap
      _ = _ := hsqrt
  linarith

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
    bipartiteDefect μ
        (fun x => (A x).postprocess f)
        (fun x => (B x).postprocess f) ψ ≤
      bipartiteDefect μ A
        B ψ := by
  simp only [bipartiteDefect, consistencyDefect]
  simp_rw [consistency_term_eq_stateQForm]
  apply avgOver_mono
  intro x
  rw [show (∑ b : β, ∑ c : β, if b = c then 0 else
      stateQForm ψ
        (heteroKron (((A x).postprocess f).effect b) 1 *
          heteroKron 1 (((B x).postprocess f).effect c))) =
      _ by
    simpa [leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne,
      placed_product_stateQForm_eq] using
      point_defect_eq
        (leftPlacedMeasurement ((A x).postprocess f))
        (rightPlacedMeasurement ((B x).postprocess f)) ψ]
  rw [show (∑ a : α, ∑ a' : α, if a = a' then 0 else
      stateQForm ψ
        (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a'))) =
      _ by
    simpa [leftPlacedMeasurement, rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne,
      placed_product_stateQForm_eq] using
      point_defect_eq (leftPlacedMeasurement (A x))
        (rightPlacedMeasurement (B x)) ψ]
  solve_by_elim [sub_le_sub_left, diagonal_postprocess_stateQForm_ge]

/-- Formalization-only same-question specialization of
`opFamilyDistSq_mul_left_le`, obtained by pushing the question distribution
along the diagonal map. -/
private theorem opFamilyDistSq_mul_left_same_question_le {X α β γ ι : Type*}
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
  let μdiag := μ.map (fun x => (x, x))
  have hout := opFamilyDistSq_mul_left_le μdiag A B C ψ δ hC (by simpa [μdiag, opFamilyDistSq, Distribution.avgOver_map] using h)
  simpa [μdiag, opFamilyDistSq, Distribution.avgOver_map] using hout

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
  let AL : X → (α × β) → Op (ιA × ιB) :=
    fun x ab => leftTensor ((A x).effect ab)
  let DL : X → (α × γ) → Op (ιA × ιB) :=
    fun x ac => leftTensor ((D x).effect ac)
  let BAB : X → (α × β) → Op (ιA × ιB) :=
    fun x ab => rightTensor
      (((B x).postprocess (fun abc => abc.1)).effect ab)
  let BAC : X → (α × γ) → Op (ιA × ιB) :=
    fun x ac => rightTensor
      (((B x).postprocess (fun abc => (abc.1.1, abc.2))).effect ac)
  let BJ : X → ((α × β) × γ) → Op (ιA × ιB) :=
    fun x abc => rightTensor ((B x).effect abc)
  let FAD : X → ((α × β) × γ) → _ :=
    fun x abc => AL x abc.1 * DL x (abc.1.1, abc.2)
  let FDA : X → ((α × β) × γ) → _ :=
    fun x abc => DL x (abc.1.1, abc.2) * AL x abc.1
  let FMidAD : X → ((α × β) × γ) → _ :=
    fun x abc => AL x abc.1 * BAC x (abc.1.1, abc.2)
  let FMidDA : X → ((α × β) × γ) → _ :=
    fun x abc => DL x (abc.1.1, abc.2) * BAB x abc.1
  have hAB' := hAB
  have hDB' := hDB
  have hAD_mid_raw := opFamilyDistSq_mul_left_same_question_le μ DL BAC
    (fun x a b => AL x (a, b)) ψ δ (by
      intro x a
      apply left_fiber_contraction) hDB'
  have hAD_mid : opFamilyDistSq μ FAD FMidAD ψ ≤ δ := by
    rw [opFamilyDistSq_reindex μ (swapLast α β γ)] at hAD_mid_raw
    assumption
  have hmid_AD_joint_raw := opFamilyDistSq_mul_left_same_question_le μ AL BAB
    (fun x a c => BAC x (a, c)) ψ δ (by
      intro x a
      apply right_fiber_contraction) hAB'
  have hmid_AD_joint : opFamilyDistSq μ FMidAD BJ ψ ≤ δ := by
    have hcross (x : X) (abc : (α × β) × γ) :
        BAC x (abc.1.1, abc.2) * AL x abc.1 =
          AL x abc.1 * BAC x (abc.1.1, abc.2) :=
      (left_right_commute _ _).symm
    have hcollapse (x : X) (abc : (α × β) × γ) :
        BAC x (abc.1.1, abc.2) * BAB x abc.1 = BJ x abc := by
      rw [rightTensor_mul_rightTensor]
      exact congrArg _
        (joint_marginal_product_rev _ (hB x)
          abc.1.1 abc.1.2 abc.2)
    simpa [FMidAD, hcross, hcollapse] using hmid_AD_joint_raw
  have hAD_joint : opFamilyDistSq μ FAD BJ ψ ≤ 4 * δ := by
    have h := opFamilyDistSq_le_of_le_of_le FAD FMidAD BJ ψ δ δ
      hAD_mid hmid_AD_joint
    linarith
  have hDA_mid_raw := opFamilyDistSq_mul_left_same_question_le μ AL BAB
    (fun x a c => DL x (a, c)) ψ δ (by
      intro x a
      apply left_fiber_contraction) hAB'
  have hDA_mid := hDA_mid_raw
  have hmid_DA_joint_raw :=
    opFamilyDistSq_mul_left_same_question_le μ DL BAC
      (fun x a b => BAB x (a, b)) ψ δ (by
        intro x a
        apply right_fiber_contraction) hDB'
  have hmid_DA_joint : opFamilyDistSq μ FMidDA BJ ψ ≤ δ := by
    have hcross (x : X) (abc : (α × β) × γ) :
        BAB x abc.1 * DL x (abc.1.1, abc.2) =
          _ * BAB x abc.1 :=
      (left_right_commute _ _).symm
    have hcollapse (x : X) (abc : (α × β) × γ) :
        BAB x abc.1 * BAC x (abc.1.1, abc.2) = BJ x abc := by
      rw [rightTensor_mul_rightTensor]
      exact congrArg _
        (joint_marginal_product (hB x)
          abc.1.1 abc.1.2 abc.2)
    calc
      _ = _ := (opFamilyDistSq_congr μ _ _ FMidDA BJ ψ hcross hcollapse).symm
      _ ≤ δ := (by
        calc
          _ =
            opFamilyDistSq μ
              (fun x (acb : (α × γ) × β) =>
                BAB x (acb.1.1, acb.2) * DL x acb.1)
              (fun x (acb : (α × γ) × β) =>
                BAB x (acb.1.1, acb.2) * BAC x acb.1) ψ := by
              simpa only [swapLast_symm_apply] using
                (opFamilyDistSq_reindex μ (swapLast α β γ)
                  (fun x (acb : (α × γ) × β) =>
                    BAB x (acb.1.1, acb.2) * DL x acb.1)
                  (fun x (acb : (α × γ) × β) =>
                    BAB x (acb.1.1, acb.2) * BAC x acb.1) ψ).symm
          _ ≤ δ := hmid_DA_joint_raw)
  have hjoint_DA : opFamilyDistSq μ BJ FDA ψ ≤ 4 * δ := by
    rw [← opFamilyDistSq_symm]
    have h := opFamilyDistSq_le_of_le_of_le FDA FMidDA BJ ψ δ δ
      hDA_mid hmid_DA_joint
    linarith
  have hcomm := opFamilyDistSq_le_of_le_of_le FAD BJ FDA ψ
    _ _ hAD_joint hjoint_DA
  calc
    _ = _ := by
      apply opFamilyDistSq_congr_sub
      intro x abc
      change _ =
        leftTensor (ι₂ := ιB) ((A x).effect abc.1) *
            leftTensor (ι₂ := ιB) ((D x).effect (abc.1.1, abc.2)) -
          leftTensor (ι₂ := ιB) ((D x).effect (abc.1.1, abc.2)) *
            leftTensor (ι₂ := ιB) ((A x).effect abc.1)
      simp [leftTensor_mul_leftTensor, sub_zero]
      exact (leftTensor_sub _ _).symm
    _ ≤ 16 * δ := (by linarith)

/-- Joint closeness to a projective refinement on the left tensor factor
implies approximate commutation of the corresponding right-factor POVMs.

This is a formalization-only auxiliary, not a named statement of the paper: it
is the right-register form of `lem:commutation-analysis`, blueprint
`ch12_qpbt_games.tex:403-416`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:410-461`, with the
same explicit constant. It is stated on the right factor because the pasting
conclusion of `lem:pasting` carries the codeword families there. It supplies the
constant of `exists_coarse_commutator_bound`, the coarse commutator estimate of
the proof of `exists_pasting_error`. -/
theorem op_dist_sq_commutator_right_le_explicit :
    ∀ {X α β γ ιA ιB : Type*}
      [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
      [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
      (μ : Distribution X)
      (A : X → Measurement (α × β) ιB)
      (B : X → Measurement ((α × β) × γ) ιA)
      (D : X → Measurement (α × γ) ιB)
      (ψ : EuclideanSpace ℂ (ιA × ιB)) (δ : ℝ),
      (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x)) →
      opFamilyDistSq μ
        (fun x ab => heteroKron (((B x).postprocess
          (fun abc => abc.1)).effect ab) 1)
        (fun x ab => heteroKron 1 ((A x).effect ab)) ψ ≤ δ →
      opFamilyDistSq μ
        (fun x ac => heteroKron (((B x).postprocess
          (fun abc => (abc.1.1, abc.2))).effect ac) 1)
        (fun x ac => heteroKron 1 ((D x).effect ac)) ψ ≤ δ →
      opFamilyDistSq μ
        (fun x (abc : (α × β) × γ) => heteroKron 1
          (((A x).effect (abc.1.1, abc.1.2)) * ((D x).effect (abc.1.1, abc.2)) -
            ((D x).effect (abc.1.1, abc.2)) * ((A x).effect (abc.1.1, abc.1.2))))
        (fun _ _ => 0) ψ ≤ 16 * δ := by
  intro X α β γ ιA ιB _ _ _ _ _ _ _ _ _ _ μ A B D ψ δ hB hBA hBD
  have h := op_dist_sq_commutator_le_explicit μ A B D
    (reindexState (Equiv.prodComm ιA ιB) ψ) δ hB
  simp [WinImplications.opFamilyDistSq_reindexState, WinImplications.reindexOp_prodComm_heteroKron] at h
  apply h <;> rwa [opFamilyDistSq_symm]

end MIPStarRE.QPBT
