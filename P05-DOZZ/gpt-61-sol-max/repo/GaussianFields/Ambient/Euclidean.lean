/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# GaussianFields.Ambient/Euclidean

Port of the corresponding GaussianFields source module.
-/

public section

open scoped BigOperators

namespace GaussianFields

/-- The standalone model of `R^d` for Gaussian fields. -/
abbrev Vec (d : Nat) := Fin d → ℝ

/-- The Euclidean dot product on `Vec d`. -/
@[expose]
noncomputable def euclideanDot {d : Nat} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

variable {d : Nat} (x : Vec d)

include d x in
/-- The squared Euclidean norm on `Vec d`. -/
@[expose]
noncomputable def euclideanNormSq  : ℝ :=
  euclideanDot x x

include d x in
/-- The Euclidean norm on `Vec d`. -/
@[expose]
noncomputable def euclideanNorm  : ℝ :=
  Real.sqrt (euclideanNormSq x)



@[simp]
theorem euclideanDot_apply {d : Nat} (x y : Vec d) :
    euclideanDot x y = ∑ i, x i * y i :=
  rfl

include d x in
theorem euclideanNormSq_eq_sum  :
    euclideanNormSq x = ∑ i, x i * x i :=
  rfl

include d x in
theorem euclideanNorm_nonneg  :
    0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

/-- The squared Euclidean norm is continuous. -/
theorem continuous_euclideanNormSq {d : Nat} :
    Continuous (fun x : Vec d => euclideanNormSq x) := by
  unfold euclideanNormSq euclideanDot
  fun_prop

/-- The local Euclidean norm is continuous. -/
theorem continuous_euclideanNorm {d : Nat} :
    Continuous (fun x : Vec d => euclideanNorm x) := Real.continuous_sqrt.comp continuous_euclideanNormSq

include d x
/-- The local Euclidean norm is bounded by the coordinate `L^1` norm. -/
theorem euclideanNorm_le_sum_abs  :
    euclideanNorm x ≤ ∑ i : Fin d, |x i| := by
  unfold euclideanNorm euclideanNormSq euclideanDot
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun i _hi => abs_nonneg (x i)
  · calc
      ∑ i : Fin d, x i * x i
          = ∑ i : Fin d, |x i| ^ (2 : Nat) := by
            grind
      _ ≤ (∑ i : Fin d, |x i|) ^ (2 : Nat) := Finset.sum_sq_le_sq_sum_of_nonneg
              (s := Finset.univ) (f := fun i : Fin d => |x i|)
              (fun i _hi => abs_nonneg (x i))


/-- Each coordinate is bounded by the local Euclidean norm. -/
theorem abs_apply_le_euclideanNorm  (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanNormSq euclideanDot
  refine Real.abs_le_sqrt ?_
  calc
    x i ^ (2 : Nat) = x i * x i := by ring_nf
    _ ≤ ∑ j : Fin d, x j * x j := Finset.single_le_sum
            (s := Finset.univ) (f := fun j : Fin d => x j * x j)
            (fun j _hj => by nlinarith [sq_nonneg (x j)])
            (Finset.mem_univ i)


/-- Mathlib's finite-product sup norm is bounded by the local Euclidean norm. -/
theorem norm_le_euclideanNorm  :
    ‖x‖ ≤ euclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg x)]
  intro i
  exact abs_apply_le_euclideanNorm x i


/-- The local Euclidean norm is bounded by `d` times Mathlib's finite-product sup norm. -/
theorem euclideanNorm_le_card_mul_norm  :
    euclideanNorm x ≤ (d : ℝ) * ‖x‖ := by
  calc
    euclideanNorm x ≤ ∑ i : Fin d, |x i| := euclideanNorm_le_sum_abs x
    _ = ∑ i : Fin d, ‖x i‖ := by
          simp_all
    _ ≤ Fintype.card (Fin d) • ‖x‖ := Pi.sum_norm_apply_le_norm (f := x)
    _ = (d : ℝ) * ‖x‖ := by
          simp_all
omit d x


theorem euclideanNormSq_smul {d : Nat} (c : ℝ) (x : Vec d) :
    euclideanNormSq (c • x) = c ^ 2 * euclideanNormSq x := by
  rw [euclideanNormSq_eq_sum, euclideanNormSq_eq_sum]
  calc
    (∑ i, (c • x) i * (c • x) i) = ∑ i, c ^ 2 * (x i * x i) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c ^ 2 * ∑ i, x i * x i := by
      rw [Finset.mul_sum]

theorem euclideanNorm_smul {d : Nat} (c : ℝ) (x : Vec d) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg c)]
  rw [Real.sqrt_sq_eq_abs]

include d x in
theorem euclideanNormSq_neg  :
    euclideanNormSq (-x) = euclideanNormSq x := by
  rw [← neg_one_smul ℝ x, euclideanNormSq_smul]
  norm_num

include d x in
theorem euclideanNorm_neg  :
    euclideanNorm (-x) = euclideanNorm x := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_neg]

theorem euclideanNormSq_sub_comm {d : Nat} (x y : Vec d) :
    euclideanNormSq (x - y) = euclideanNormSq (y - x) := by
  have hxy : x - y = -(y - x) := by
    simp_all
  rw [hxy, euclideanNormSq_neg]

theorem euclideanNorm_sub_comm {d : Nat} (x y : Vec d) :
    euclideanNorm (x - y) = euclideanNorm (y - x) := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_sub_comm]

include d x in
theorem euclideanNorm_inv_smul  (r : ℝ) :
    euclideanNorm (r⁻¹ • x) = |r⁻¹| * euclideanNorm x :=
  euclideanNorm_smul r⁻¹ x

end GaussianFields

end
