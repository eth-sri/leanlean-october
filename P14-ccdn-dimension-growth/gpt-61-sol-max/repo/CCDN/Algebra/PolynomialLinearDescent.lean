/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib
import CCDN.ForMathlib.MvPolynomial

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Coefficientwise application of a linear map to multivariate polynomials, and
linear coefficient descent of a polynomial over a field extension: a nonzero
polynomial vanishing at base-field points has a nonzero base-field polynomial of no
larger degree vanishing at every one of those points. -/

@[expose] public section
namespace CCDN
open MvPolynomial Module

/-- A reducible coefficient extension of an irreducible polynomial has two
nonzero factors of positive degree. -/
lemma exists_proper_polynomial_factors {k K σ : Type*}
    [Field k] [Field K] [Algebra k K]
    (f : MvPolynomial σ k) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ g h : MvPolynomial σ K, map (algebraMap k K) f = g * h ∧
      g ≠ 0 ∧ h ≠ 0 ∧ 0 < g.totalDegree ∧ 0 < h.totalDegree := by
  have hmap0 : map (algebraMap k K) f ≠ 0 := by
    simpa only [map_zero] using (map_injective (algebraMap k K) (algebraMap k K).injective).ne hir.ne_zero
  have hmapu : ¬ IsUnit (map (algebraMap k K) f) := by
    intro hu
    have hz := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [totalDegree_map_of_injective (algebraMap k K).injective] at hz
    exact (totalDegree_pos_of_irreducible hir).ne' hz
  simp [irreducible_iff, hmapu] at hred
  obtain ⟨g, h, hfac, hgu, hhu⟩ := hred
  have hg0 : g ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hh0 : h ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  exact ⟨g, h, hfac, hg0, hh0, totalDegree_pos_of_ne_zero_of_not_isUnit hg0 hgu,
    totalDegree_pos_of_ne_zero_of_not_isUnit hh0 hhu⟩

variable {R A B σ : Type*} [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₗ[R] B)

/-- Apply a linear coefficient map without changing any monomial. -/
noncomputable def polynomialCoefficientLinear  : MvPolynomial σ A →ₗ[R] MvPolynomial σ B :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap φ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- Each coefficient of `polynomialCoefficientLinear φ f` is the image under `φ` of the
corresponding coefficient of `f`. -/
@[simp] lemma polynomialCoefficientLinear_coeff  (f : MvPolynomial σ A) (e : σ →₀ ℕ) :
    (polynomialCoefficientLinear φ f).coeff e = φ (f.coeff e) := rfl

/-- Applying the linear map `φ` coefficientwise sends the constant `C a` to `C (φ a)`. -/
@[simp] lemma polynomialCoefficientLinear_C  (a : A) :
    polynomialCoefficientLinear (σ := σ) φ (C a) = C (φ a) := by
  classical
  ext e
  simp only [polynomialCoefficientLinear_coeff, coeff_C]
  split_ifs <;> simp

/-- If `φ (a * θ b) = φ a * b` for a ring map `θ : B →+* A`, then applying `φ` coefficientwise
is linear over polynomials with coefficients in `B`: it sends `f * map θ g` to
`polynomialCoefficientLinear φ f * g`. -/
lemma polynomialCoefficientLinear_mul_compatible  (θ : B →+* A)
    (hφ : ∀ a b, φ (a * θ b) = φ a * b)
    (f : MvPolynomial σ A) (g : MvPolynomial σ B) :
    polynomialCoefficientLinear φ (f * map θ g) =
      polynomialCoefficientLinear φ f * g := by
  classical
  ext e
  rw [polynomialCoefficientLinear_coeff, coeff_mul, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_map, polynomialCoefficientLinear_coeff, hφ]

/-- For a field extension `L / K` and a `K`-linear functional `φ : L → K`, applying `φ`
coefficientwise is linear over polynomials with coefficients in `K`: it sends
`f * map (algebraMap K L) g` to `polynomialCoefficientLinear φ f * g`. -/
lemma polynomialCoefficientLinear_mul_map {K L σ : Type*}
    [Field K] [Field L] [Algebra K L]
    (φ : L →ₗ[K] K) (f : MvPolynomial σ L) (g : MvPolynomial σ K) :
    polynomialCoefficientLinear φ (f * map (algebraMap K L) g) =
      polynomialCoefficientLinear φ f * g := by
  apply polynomialCoefficientLinear_mul_compatible
  intro a b
  simpa only [Algebra.smul_def, smul_eq_mul, mul_comm, Algebra.algebraMap_self,
    RingHom.id_apply] using φ.map_smul b a


/-- For a field extension `K / k` and a `k`-linear functional `φ : K → k`, evaluating the
coefficientwise image of `f` under `φ` at a `k`-point `x` gives `φ` of the value of `f` at `x`. -/
lemma polynomialCoefficientLinear_eval {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    (φ : K →ₗ[k] k) (f : MvPolynomial σ K) (x : σ → k) :
    eval x (polynomialCoefficientLinear φ f) = φ (eval (algebraMap k K ∘ x) f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    have hX : (X j : MvPolynomial σ K) = map (algebraMap k K) (X j) := by simp
    rw [hX, polynomialCoefficientLinear_mul_map, map_X]
    simp only [map_mul, eval_X, hf, Function.comp_apply]
    rw [mul_comm _ (algebraMap k K (x j)), ← Algebra.smul_def, φ.map_smul, smul_eq_mul, mul_comm]

/-- Linear coefficient descent: for a field extension `K / k`, a nonzero polynomial `f` over `K`
has a nonzero polynomial over `k` of total degree at most that of `f` vanishing at every
`k`-point where `f` vanishes. -/
theorem exists_nonzero_polynomial_linear_descent {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) :
    ∃ g : MvPolynomial (Fin n) k, g ≠ 0 ∧ g.totalDegree ≤ f.totalDegree ∧
      ∀ x : Fin n → k, eval (algebraMap k K ∘ x) f = 0 → eval x g = 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hm
  refine ⟨polynomialCoefficientLinear φ f, ?_,
    (by
      classical
      apply Finset.sup_le
      intro m hm
      apply le_totalDegree
      rw [MvPolynomial.mem_support_iff, polynomialCoefficientLinear_coeff] at hm
      rw [MvPolynomial.mem_support_iff]
      intro hz
      exact hm (by rw [hz, map_zero])), ?_⟩
  · intro he
    have hh := polynomialCoefficientLinear_coeff φ f m
    have hz := by simpa [he] using hh.symm
    exact hφ hz
  · intro x hx
    rw [polynomialCoefficientLinear_eval, hx, map_zero]

end CCDN
