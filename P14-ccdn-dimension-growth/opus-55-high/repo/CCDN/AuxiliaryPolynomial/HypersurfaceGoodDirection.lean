/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.ForMathlib.MvPolynomial

/-! Simultaneous avoidance of the top homogeneous form, a tangent hyperplane,
and a chosen coordinate hyperplane, by a direction over the base field. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K σ : Type*} [Field K] [Fintype σ] (f : MvPolynomial σ K)

/-- The linear form evaluating a differential on a direction. -/
def tangentDirectionPolynomial
    (z : σ → K) : MvPolynomial σ K :=
  ∑ i, C (eval z (pderiv i f)) * X i

lemma tangentDirectionPolynomial_coeff
    (z : σ → K) (j : σ) :
    (tangentDirectionPolynomial f z).coeff (Finsupp.single j 1) = eval z (pderiv j f) := by
  classical
  simp [tangentDirectionPolynomial, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff]

lemma tangentDirectionPolynomial_eval
    (z b : σ → K) :
    eval b (tangentDirectionPolynomial f z) = ∑ i, eval z (pderiv i f) * b i := by
  simp [tangentDirectionPolynomial]

end

/-- Over an infinite field, a smooth point admits a direction with nonzero
leading form, nonzero directional derivative, and nonzero selected coordinate. -/
theorem exists_good_hypersurface_direction_with_coordinate
    {K σ : Type*} [Field K] [Infinite K] [Fintype σ]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (z : σ → K)
    (j : σ) (hj : eval z (pderiv j f) ≠ 0) (k : σ) :
    ∃ b : σ → K, b k ≠ 0 ∧
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      (∑ i, eval z (pderiv i f) * b i) ≠ 0 := by
  let H := homogeneousComponent f.totalDegree f
  let T := tangentDirectionPolynomial f z
  have hH := homogeneousComponent_totalDegree_ne_zero hf
  have hT : T ≠ 0 := by
    intro h
    have hc := congrArg (fun g => g.coeff (Finsupp.single j 1)) h
    rw [tangentDirectionPolynomial_coeff] at hc
    simp_all
  have hprod := mul_ne_zero (mul_ne_zero hH hT) (X_ne_zero k)
  have hhom : (H * T * X k).IsHomogeneous (f.totalDegree + 1 + 1) :=
    ((homogeneousComponent_isHomogeneous _ _).mul
      (show (tangentDirectionPolynomial f z).IsHomogeneous 1 by
          exact IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X _ i))).mul (isHomogeneous_X K k)
  have hex : ∃ b : σ → K, eval b (H * T * X k) ≠ 0 := by
    by_contra! hn
    exact hprod (hhom.eq_zero_of_forall_eval_eq_zero hn)
  obtain ⟨b, hb⟩ := hex
  rw [map_mul, map_mul, eval_X] at hb
  refine ⟨b, right_ne_zero_of_mul hb, left_ne_zero_of_mul (left_ne_zero_of_mul hb), ?_⟩
  rw [← tangentDirectionPolynomial_eval]
  exact right_ne_zero_of_mul (left_ne_zero_of_mul hb)

