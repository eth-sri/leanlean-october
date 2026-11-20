/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Translation of multivariate polynomials by a point: `originShift a` substitutes
`X j + a j` for every variable, moving the point `a` to the origin. `originShiftEquiv a` is
the same substitution as an algebra automorphism, with inverse the shift by `-a`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The substitution `X j ↦ X j + a j`, which moves the point `a` to the origin. -/
def originShift {R σ : Type*} [CommRing R] (a : σ → R) :
    MvPolynomial σ R →+* MvPolynomial σ R := eval₂Hom C (fun j => X j + C (a j))

section

variable {R σ : Type*} [CommRing R] (a : σ → R)
include R σ a

/-- The origin shift fixes constant polynomials. -/
@[simp] lemma originShift_C (c : R) :
    originShift a (C c) = C c := by
  simp [originShift]

/-- The origin shift by `a` sends the variable `X j` to `X j + a j`. -/
@[simp] lemma originShift_X (j : σ) :
    originShift a (X j) = X j + C (a j) := by
  simp [originShift]

end

/-- The substitution `X j ↦ X j + a j` as an algebra automorphism, with inverse the
substitution `X j ↦ X j - a j`. -/
def originShiftEquiv {R σ : Type*} [CommRing R] (a : σ → R) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval fun j => X j + C (a j)) (aeval fun j => X j + C ((-a) j))
    (by aesop)
    (by aesop)

section

variable {R σ : Type*} [CommRing R] (a : σ → R)
include R σ a

/-- The origin shift is injective. -/
lemma originShift_injective :
    Function.Injective (originShift a) :=
  (originShiftEquiv a).injective

/-- The origin shift of a nonzero polynomial is nonzero. -/
lemma originShift_ne_zero
    {f : MvPolynomial σ R} (hf : f ≠ 0) : originShift a f ≠ 0 :=
  (map_ne_zero_iff _ (originShift_injective a)).2 hf

end

/-- The origin shift commutes with coefficient maps: mapping the coefficients of the shift of `f`
by `a` along `φ` gives the shift of the mapped polynomial by the mapped point `φ ∘ a`. -/
lemma originShift_map {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : σ → R) (f : MvPolynomial σ R) :
    map φ (originShift a f) = originShift (fun j => φ (a j)) (map φ f) := by
  simp [originShift, map_eval₂, Function.comp_def]

section

variable {R σ : Type*} [CommRing R]
include R σ

/-- Evaluate a translated polynomial by translating the point. -/
lemma eval_originShift (a x : σ → R)
    (f : MvPolynomial σ R) :
    eval x (originShift a f) = eval (fun j => x j + a j) f := by
  simp [originShift, ← eval_assoc, Function.comp_def]

/-- Evaluating the origin shift of `f` by `a` at `x - a` gives the value of `f` at `x`. -/
lemma eval_sub_originShift (a x : σ → R)
    (f : MvPolynomial σ R) :
    eval (fun j => x j - a j) (originShift a f) = eval x f := by
  simp [eval_originShift]

/-- The origin shift of `f` by `a` takes at the origin the value of `f` at `a`. -/
lemma eval_zero_originShift (a : σ → R)
    (f : MvPolynomial σ R) : eval (0 : σ → R) (originShift a f) = eval a f := by
  simp only [eval_originShift, Pi.zero_apply, zero_add]

lemma originShift_totalDegree_le
    (a : σ → R) (f : MvPolynomial σ R) : (originShift a f).totalDegree ≤ f.totalDegree := by
  exact linear_eval₂_totalDegree_le (.id R) _ (fun j => (totalDegree_add _ _).trans (by simpa using (isHomogeneous_X R j).totalDegree_le)) f

/-- Translation preserves the entire degree-`d` component when no higher degrees are present. -/
lemma homogeneousComponent_originShift_of_le [IsDomain R]
    (a : σ → R) (f : MvPolynomial σ R) (d : ℕ) (hd : f.totalDegree ≤ d) :
    homogeneousComponent d (originShift a f) = homogeneousComponent d f := by
  classical
  have hm (s : σ →₀ ℕ) (c : R) : ∀ k ≥ (monomial s c).totalDegree,
      homogeneousComponent k (originShift a (monomial s c)) = homogeneousComponent k (monomial s c) := by
    refine induction_on_monomial (motive := fun p => ∀ k ≥ p.totalDegree,
      homogeneousComponent k (originShift a p) = homogeneousComponent k p) ?_ ?_ s c
    · simp
    · intro g i ih k hk
      by_cases hg : g = 0
      · simp [hg]
      rw [totalDegree_mul_of_isDomain hg (X_ne_zero i), totalDegree_X] at hk
      obtain ⟨j, rfl⟩ : ∃ j, k = 1 + j := ⟨k - 1, by omega⟩
      rw [map_mul, originShift_X, mul_add, map_add, mul_comm g (X i),
        mul_comm (originShift a g) (X i),
        homogeneousComponent_mul_of_isHomogeneous_left (isHomogeneous_X _ _),
        homogeneousComponent_mul_of_isHomogeneous_left (isHomogeneous_X _ _), ih j (by omega),
        homogeneousComponent_eq_zero (1 + j) _ (show _ < _ from ?_), add_zero]
      have h := (totalDegree_mul (originShift a g) (C (a i))).trans
        (Nat.add_le_add_right (originShift_totalDegree_le a g) _)
      rw [totalDegree_C] at h
      omega
  conv_lhs => rw [f.as_sum, map_sum, map_sum]
  conv_rhs => rw [f.as_sum, map_sum]
  exact Finset.sum_congr rfl fun s hs => hm s _ _ ((totalDegree_monomial_le _ _).trans ((le_totalDegree hs).trans hd))

/-- The origin shift commutes with partial derivatives. -/
lemma pderiv_originShift (a : σ → R)
    (f : MvPolynomial σ R) (j : σ) :
    pderiv j (originShift a f) = originShift a (pderiv j f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp_all
  | mul_X f k hf =>
    simp only [map_mul, pderiv_mul, map_add, hf]
    by_cases h : k = j <;> aesop

end

end
end CCDN
