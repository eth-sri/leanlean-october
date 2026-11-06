/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ForMathlib.IntegerPolynomialL1
import CCDN.Noether.AmbientNoetherForms
import CCDN.Noether.UniversalPlaneL1

/-!
The printed coefficient-sum bound for the ambient Noether forms.
Coefficient extraction from plane parameters costs no additional factor.

The sharp printed coefficient-sum bound for the plane Noether minors:
each entry has l1 norm at most d, hence the order d²−1 determinant has
l1 norm at most d^(3d²−3).
-/

namespace CCDN
section

lemma factorial_mul_degree_pow_le (d r : ℕ) (hr : r ≤ d ^ 2) :
    r.factorial * d ^ r ≤ d ^ (3 * r) := by
  calc
    r.factorial * d ^ r ≤ r ^ r * d ^ r :=
      Nat.mul_le_mul_right _ (Nat.factorial_le_pow r)
    _ ≤ (d ^ 2) ^ r * d ^ r :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hr r)
    _ = d ^ (3 * r) := by
      rw [← pow_mul, ← pow_add]
      grind

open MvPolynomial

lemma ambientEulerEntry_flatten_l1_le (σ : Type*) [Fintype σ] [DecidableEq σ]
    (k : ℕ) (row : ℕ × ℕ) (col : EulerColumns k) :
    l1Norm ((sumAlgEquiv ℤ (PlaneParameters σ) (Sym σ (k + 2))).symm
      (ambientEulerEntryLinear _ σ k row col (universalHomogeneousForm σ (k + 2)))) ≤
      Fintype.card (Sym σ (k + 2)) * ((k + 2) * 3 ^ (k + 2)) := by
  rw [universalHomogeneousForm_linear_expansion, map_sum, map_sum]
  apply (l1Norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Sym σ (k + 2), (k + 2) * 3 ^ (k + 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, ambientEulerEntryLinear_map, smul_eq_C_mul]
      exact (l1Norm_sumAlgEquiv_symm_C_X_mul_map_C_le _ i).trans
        (ambientEulerEntry_monomial_l1_le k _ (homogeneousCoefficientExponent_degree _ _ _) row col)
    _ = _ := by simp

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ) (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k)

