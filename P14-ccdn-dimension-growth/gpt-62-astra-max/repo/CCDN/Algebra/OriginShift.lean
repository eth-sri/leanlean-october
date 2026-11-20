/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees

/-! Translation of multivariate polynomials by a point: `originShift a` substitutes
`X j + a j` for every variable, moving the point `a` to the origin. `originShiftEquiv a` is
the same substitution as an algebra automorphism, with inverse the shift by `-a`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {R S σ τ : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a x : σ → R)
    (f : MvPolynomial σ R) (j : σ)

/-- The substitution `X j ↦ X j + a j`, which moves the point `a` to the origin. -/
def originShift :
    MvPolynomial σ R →+* MvPolynomial σ R := eval₂Hom C (fun j => X j + C (a j))

/-- The origin shift fixes constant polynomials. -/
@[simp] lemma originShift_C (c : R) :
    originShift a (C c) = C c := by
  simp [originShift]

/-- The origin shift by `a` sends the variable `X j` to `X j + a j`. -/
@[simp] lemma originShift_X :
    originShift a (X j) = X j + C (a j) := by
  simp [originShift]

private lemma originShift_neg :
    originShift (-a) (originShift a f) = f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp_all
  | mul_X f j hf => simp [hf]

/-- The substitution `X j ↦ X j + a j` as an algebra automorphism, with inverse the
substitution `X j ↦ X j - a j`. -/
def originShiftEquiv :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval fun j => X j + C (a j)) (aeval fun j => X j + C ((-a) j))
    (by apply MvPolynomial.algHom_ext; intro j; simp)
    (by apply MvPolynomial.algHom_ext; intro j; simp)

/-- The automorphism `originShiftEquiv a` acts as the origin shift `originShift a`. -/
@[simp] lemma originShiftEquiv_apply : originShiftEquiv a f = originShift a f :=
  rfl

/-- The inverse of `originShiftEquiv a` acts as the origin shift by `-a`. -/
@[simp] lemma originShiftEquiv_symm_apply : (originShiftEquiv a).symm f = originShift (-a) f :=
  rfl

/-- The origin shift is injective. -/
lemma originShift_injective :
    Function.Injective (originShift a) :=
  Function.LeftInverse.injective (originShift_neg a)

/-- The origin shift of a nonzero polynomial is nonzero. -/
lemma originShift_ne_zero
    {f : MvPolynomial σ R} (hf : f ≠ 0) : originShift a f ≠ 0 :=
  (by solve_by_elim [originShift_injective])

/-- The origin shift commutes with coefficient maps: mapping the coefficients of the shift of `f`
by `a` along `φ` gives the shift of the mapped polynomial by the mapped point `φ ∘ a`. -/
lemma originShift_map :
    map φ (originShift a f) = originShift (fun j => φ (a j)) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [*]
  | mul_X f j hf => simp [hf]

private lemma eval_originShift :
    eval x (originShift a f) = eval (fun j => x j + a j) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp_all
  | mul_X f j hf => simp [hf]

/-- Evaluating the origin shift of `f` by `a` at `x - a` gives the value of `f` at `x`. -/
lemma eval_sub_originShift :
    eval (fun j => x j - a j) (originShift a f) = eval x f := by
  simp [eval_originShift]

/-- The origin shift of `f` by `a` takes at the origin the value of `f` at `a`. -/
lemma eval_zero_originShift : eval (0 : σ → R) (originShift a f) = eval a f := by
  rw [eval_originShift]
  simp

/-- The origin shift commutes with partial derivatives. -/
lemma pderiv_originShift :
    pderiv j (originShift a f) = originShift a (pderiv j f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp_all
  | mul_X f k hf =>
    simp only [map_mul, pderiv_mul, map_add, hf]
    by_cases h : k = j
    · subst k
      simp
    · simp [pderiv_X_of_ne h]

/-- Substituting affine linear polynomials does not increase total degree. -/
theorem linear_eval₂_totalDegree_le (g : σ → MvPolynomial τ S) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (f : MvPolynomial σ R) :
    (eval₂Hom (C.comp φ) g f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial, RingHom.comp_apply]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  calc _ ≤ ∑ j ∈ e.support, (g j ^ e j).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ j ∈ e.support, e j := by
      apply Finset.sum_le_sum
      intro j _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (e j) (hg j))
    _ ≤ f.totalDegree := le_totalDegree he

/-- Translation by constants does not increase degree. -/
theorem originShift_totalDegree_le [Nontrivial R]
    (a : σ → R) (f : MvPolynomial σ R) : (originShift a f).totalDegree ≤ f.totalDegree :=
  linear_eval₂_totalDegree_le (RingHom.id R) _ (fun j =>
    (totalDegree_add (X j) (C (a j))).trans (by simp)) f

end
end CCDN
