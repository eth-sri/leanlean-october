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

/-- The squared Euclidean norm on `Vec d`. -/
@[expose]
noncomputable def euclideanNormSq {d : Nat} (x : Vec d) : ℝ :=
  euclideanDot x x

/-- The Euclidean norm on `Vec d`. -/
@[expose]
noncomputable def euclideanNorm {d : Nat} (x : Vec d) : ℝ :=
  Real.sqrt (euclideanNormSq x)
section
variable {d : Nat}


section
variable (x : Vec d)

theorem euclideanNormSq_eq_sum :
    euclideanNormSq x = ∑ i, x i * x i :=
  rfl

theorem euclideanNorm_nonneg :
    0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

end

/-- The squared Euclidean norm is continuous. -/
theorem continuous_euclideanNormSq :
    Continuous (fun x : Vec d => euclideanNormSq x) := by
  unfold euclideanNormSq euclideanDot
  fun_prop

/-- The local Euclidean norm is continuous. -/
theorem continuous_euclideanNorm :
    Continuous (fun x : Vec d => euclideanNorm x) := by
  exact Real.continuous_sqrt.comp continuous_euclideanNormSq

end
section
variable {d : Nat} (x : Vec d)

/-- The local Euclidean norm is bounded by the coordinate `L^1` norm. -/
theorem euclideanNorm_le_sum_abs :
    euclideanNorm x ≤ ∑ i : Fin d, |x i| := by
  unfold euclideanNorm euclideanNormSq euclideanDot
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      ∑ i : Fin d, x i * x i
          = ∑ i : Fin d, |x i| ^ 2 := by
            grind
      _ ≤ (∑ i : Fin d, |x i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg
             
              (fun i _hi => abs_nonneg (x i))

/-- Each coordinate is bounded by the local Euclidean norm. -/
theorem abs_apply_le_euclideanNorm (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanNormSq euclideanDot
  refine Real.abs_le_sqrt ?_
  calc
    x i ^ 2 = x i * x i := by ring_nf
    _ ≤ ∑ j : Fin d, x j * x j := Finset.single_le_sum
            (f := fun j : Fin d => x j * x j)
            (fun j _hj => by nlinarith)
            (Finset.mem_univ i)

/-- Mathlib's finite-product sup norm is bounded by the local Euclidean norm. -/
theorem norm_le_euclideanNorm :
    ‖x‖ ≤ euclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg x)]
  intro i
  simpa using abs_apply_le_euclideanNorm x i

/-- The local Euclidean norm is bounded by `d` times Mathlib's finite-product sup norm. -/
theorem euclideanNorm_le_card_mul_norm :
    euclideanNorm x ≤ (d : ℝ) * ‖x‖ := by
  calc
    euclideanNorm x ≤ ∑ i : Fin d, |x i| := euclideanNorm_le_sum_abs x
    _ = ∑ i : Fin d, ‖x i‖ := by
          rfl
    _ ≤ Fintype.card (Fin d) • ‖x‖ := Pi.sum_norm_apply_le_norm (f := x)
    _ = d * ‖x‖ := by
          simp

end
section
variable {d : Nat} (c : ℝ) (x : Vec d)

theorem euclideanNormSq_smul :
    euclideanNormSq (c • x) = c ^ 2 * euclideanNormSq x := by
  rw [euclideanNormSq_eq_sum, euclideanNormSq_eq_sum]
  calc
    (∑ i, (c • x) i * (c • x) i) = ∑ i, c ^ 2 * (x i * x i) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp
      ring
    _ = c ^ 2 * ∑ i, x i * x i := by
      rw [Finset.mul_sum]

theorem euclideanNorm_smul :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end
section
variable {d : Nat} (x : Vec d)

theorem euclideanNormSq_neg :
    euclideanNormSq (-x) = euclideanNormSq x := by
  rw [← neg_one_smul ℝ x, euclideanNormSq_smul]
  norm_num

theorem euclideanNorm_neg :
    euclideanNorm (-x) = euclideanNorm x := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_neg]

end
section
variable {d : Nat} (x y : Vec d)

theorem euclideanNormSq_sub_comm :
    euclideanNormSq (x - y) = euclideanNormSq (y - x) := by
  have hxy : x - y = -(y - x) := by
    simp
  rw [hxy, euclideanNormSq_neg]

theorem euclideanNorm_sub_comm :
    euclideanNorm (x - y) = euclideanNorm (y - x) := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_sub_comm]

end

theorem euclideanNorm_inv_smul {d : Nat} (x : Vec d) (r : ℝ) :
    euclideanNorm (r⁻¹ • x) = |r⁻¹| * euclideanNorm x :=
  euclideanNorm_smul r⁻¹ x

end GaussianFields

end
