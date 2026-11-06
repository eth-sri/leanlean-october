/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
/- Coordinate congruences used by projective determinant normalization. -/
module
public import CCDN.Algebra.Coordinates
import Mathlib
public section
namespace CCDN
open MvPolynomial

/-- If `x ≡ y` coordinatewise modulo `q`, then `f(x) ≡ f(y)` modulo `q` for every integer polynomial
`f`. -/
lemma dvd_eval_sub_of_dvd_coordinates {σ : Type*} (q : ℤ)
    (x y : σ → ℤ) (hxy : ∀ j, q ∣ x j - y j) (f : MvPolynomial σ ℤ) :
    q ∣ eval x f - eval y f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg =>
    simp_all [eval_add, add_sub_add_comm, dvd_add]
  | mul_X f j hf =>
    rw [eval_mul, eval_mul, eval_X, eval_X]
    exact dvd_mul_sub_mul hf (hxy j)

/-- An integer `a` coprime to `q` has an inverse `u` modulo `q`, itself coprime to `q`. -/
lemma exists_integer_inverse_of_isCoprime {q a : ℤ} (h : IsCoprime q a) :
    ∃ u : ℤ, q ∣ u * a - 1 ∧ IsCoprime q u := by
  obtain ⟨v, u, he⟩ := h
  refine ⟨u, ⟨-v, by linear_combination he⟩, v, a, ?_⟩
  simpa only [mul_comm a u] using he

end CCDN
