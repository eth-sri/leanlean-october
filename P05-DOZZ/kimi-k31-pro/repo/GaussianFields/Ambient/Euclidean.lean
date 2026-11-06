/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# GaussianFields.Ambient/Euclidean

Port of the corresponding GaussianFields source module.
-/


open scoped BigOperators

namespace GaussianFields

/-- The standalone model of `R^d` for Gaussian fields. -/
abbrev Vec (d : Nat) := Fin d → ℝ

/-- The Euclidean dot product on `Vec d`. -/

noncomputable def euclideanDot {d : Nat} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

/-- The squared Euclidean norm on `Vec d`. -/

noncomputable def euclideanNormSq {d : Nat} (x : Vec d) : ℝ :=
  euclideanDot x x

/-- The Euclidean norm on `Vec d`. -/

noncomputable def euclideanNorm {d : Nat} (x : Vec d) : ℝ :=
  Real.sqrt (euclideanNormSq x)

/-- The Euclidean distance on `Vec d`. -/

noncomputable def euclideanDist {d : Nat} (x y : Vec d) : ℝ :=
  euclideanNorm (x - y)

@[simp]
theorem euclideanDot_apply {d : Nat} (x y : Vec d) :
    euclideanDot x y = ∑ i, x i * y i :=
  rfl

theorem euclideanNormSq_eq_sum {d : Nat} (x : Vec d) :
    euclideanNormSq x = ∑ i, x i * x i :=
  rfl

theorem euclideanNorm_nonneg {d : Nat} (x : Vec d) :
    0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

/-- The squared Euclidean norm is continuous. -/
theorem continuous_euclideanNormSq {d : Nat} :
    Continuous (fun x : Vec d => euclideanNormSq x) := by
  unfold euclideanNormSq euclideanDot
  fun_prop

/-- The local Euclidean norm is continuous. -/
theorem continuous_euclideanNorm {d : Nat} :
    Continuous (fun x : Vec d => euclideanNorm x) := by
  unfold euclideanNorm
  exact Real.continuous_sqrt.comp continuous_euclideanNormSq

/-- The local Euclidean norm is bounded by the coordinate `L^1` norm. -/
theorem euclideanNorm_le_sum_abs {d : Nat} (x : Vec d) :
    euclideanNorm x ≤ ∑ i : Fin d, |x i| := by
  unfold euclideanNorm euclideanNormSq euclideanDot
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun i _hi => abs_nonneg (x i)
  · calc
      ∑ i : Fin d, x i * x i
          = ∑ i : Fin d, |x i| ^ (2 : Nat) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [sq_abs]
            ring_nf
      _ ≤ (∑ i : Fin d, |x i|) ^ (2 : Nat) := by
            exact Finset.sum_sq_le_sq_sum_of_nonneg
              (s := Finset.univ) (f := fun i : Fin d => |x i|)
              (fun i _hi => abs_nonneg (x i))

/-- Each coordinate is bounded by the local Euclidean norm. -/
theorem abs_apply_le_euclideanNorm {d : Nat} (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanNormSq euclideanDot
  refine Real.abs_le_sqrt ?_
  calc
    x i ^ (2 : Nat) = x i * x i := by ring_nf
    _ ≤ ∑ j : Fin d, x j * x j := by
          exact Finset.single_le_sum
            (s := Finset.univ) (f := fun j : Fin d => x j * x j)
            (fun j _hj => by nlinarith [sq_nonneg (x j)])
            (Finset.mem_univ i)

/-- Mathlib's finite-product sup norm is bounded by the local Euclidean norm. -/
theorem norm_le_euclideanNorm {d : Nat} (x : Vec d) :
    ‖x‖ ≤ euclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg x)]
  intro i
  simpa [Real.norm_eq_abs] using abs_apply_le_euclideanNorm x i

/-- The local Euclidean norm is bounded by `d` times Mathlib's finite-product sup norm. -/
theorem euclideanNorm_le_card_mul_norm {d : Nat} (x : Vec d) :
    euclideanNorm x ≤ (d : ℝ) * ‖x‖ := by
  calc
    euclideanNorm x ≤ ∑ i : Fin d, |x i| := euclideanNorm_le_sum_abs x
    _ = ∑ i : Fin d, ‖x i‖ := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Real.norm_eq_abs]
    _ ≤ Fintype.card (Fin d) • ‖x‖ := by
          exact Pi.sum_norm_apply_le_norm (f := x)
    _ = (d : ℝ) * ‖x‖ := by
          rw [Fintype.card_fin]
          simp [nsmul_eq_mul]

theorem euclideanNormSq_smul {d : Nat} (c : ℝ) (x : Vec d) :
    euclideanNormSq (c • x) = c ^ 2 * euclideanNormSq x := by
  rw [euclideanNormSq_eq_sum, euclideanNormSq_eq_sum]
  calc
    (∑ i, (c • x) i * (c • x) i) = ∑ i, c ^ 2 * (x i * x i) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c ^ 2 * ∑ i, x i * x i := by
      rw [Finset.mul_sum]

theorem euclideanNorm_smul {d : Nat} (c : ℝ) (x : Vec d) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem euclideanNormSq_neg {d : Nat} (x : Vec d) :
    euclideanNormSq (-x) = euclideanNormSq x := by
  rw [← neg_one_smul ℝ x, euclideanNormSq_smul]
  norm_num

theorem euclideanNorm_neg {d : Nat} (x : Vec d) :
    euclideanNorm (-x) = euclideanNorm x := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_neg]

theorem euclideanNormSq_sub_comm {d : Nat} (x y : Vec d) :
    euclideanNormSq (x - y) = euclideanNormSq (y - x) := by
  have hxy : x - y = -(y - x) := by
    ext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hxy, euclideanNormSq_neg]

theorem euclideanNorm_sub_comm {d : Nat} (x y : Vec d) :
    euclideanNorm (x - y) = euclideanNorm (y - x) := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_sub_comm]

theorem euclideanNorm_inv_smul {d : Nat} (x : Vec d) (r : ℝ) :
    euclideanNorm (r⁻¹ • x) = |r⁻¹| * euclideanNorm x :=
  euclideanNorm_smul r⁻¹ x

end GaussianFields

