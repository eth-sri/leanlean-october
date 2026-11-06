/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The homogeneous linear form `∑ i, a i * X i` with a given coefficient vector,
and its basic API: homogeneity, degree, evaluation, coefficient maps, renaming and
linearity in the coefficient vector. -/

@[expose] public section
namespace CCDN
open MvPolynomial

variable {R S σ τ : Type*}

/-- The linear form `∑ i, a i * X i` with coefficient vector `a`. -/
noncomputable def linearForm [CommSemiring R] [Fintype σ] (a : σ → R)  :=
  ∑ i, C (a i) * X i

section CommSemiring

variable [CommSemiring R] [Fintype σ]

/-- A linear form is homogeneous of degree one. -/
lemma linearForm_isHomogeneous (a : σ → R) : (linearForm a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X _ i)

/-- A linear form has total degree at most one. -/
lemma linearForm_totalDegree_le (a : σ → R) : (linearForm a).totalDegree ≤ 1 :=
  (linearForm_isHomogeneous a).totalDegree_le

/-- The linear form with coefficients `a` evaluates at `x` to `∑ i, a i * x i`. -/
@[simp] lemma eval_linearForm (a x : σ → R) : eval x (linearForm a) = ∑ i, a i * x i := by
  simp [linearForm]
















end CommSemiring




end CCDN
