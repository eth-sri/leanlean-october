/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Coefficientwise application of a linear map to multivariate polynomials, and
linear coefficient descent of a polynomial over a field extension: a nonzero
polynomial vanishing at base-field points has a nonzero base-field polynomial of no
larger degree vanishing at every one of those points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

/-- Apply a linear coefficient map without changing any monomial. -/
def polynomialCoefficientLinear {R A B σ : Type*} [CommSemiring R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) : MvPolynomial σ A →ₗ[R] MvPolynomial σ B :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap φ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- Each coefficient of `polynomialCoefficientLinear φ f` is the image under `φ` of the
corresponding coefficient of `f`. -/
@[simp] lemma polynomialCoefficientLinear_coeff {R A B σ : Type*}
    [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₗ[R] B) (f : MvPolynomial σ A) (e : σ →₀ ℕ) :
    (polynomialCoefficientLinear φ f).coeff e = φ (f.coeff e) := rfl

/-- For a field extension `k / K` and a `k`-linear functional `φ : K → k`, evaluating the
coefficientwise image of `f` under `φ` at a `k`-point `x` gives `φ` of the value of `f` at `x`. -/
lemma polynomialCoefficientLinear_eval {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    (φ : K →ₗ[k] k) (f : MvPolynomial σ K) (x : σ → k) :
    eval x (polynomialCoefficientLinear φ f) = φ (eval (algebraMap k K ∘ x) f) := by
  /- Applying the linear map `φ` coefficientwise sends the constant `C a` to `C (φ a)`. -/
  /- If `φ (a * θ b) = φ a * b` for a ring map `θ : B →+* A`, then applying `φ` coefficientwise
  is linear over polynomials with coefficients in `B`: it sends `f * map θ g` to
  `polynomialCoefficientLinear φ f * g`. -/
  /- For a field extension `L / K` and a `K`-linear functional `φ : L → K`, applying `φ`
  coefficientwise is linear over polynomials with coefficients in `K`: it sends
  `f * map (algebraMap K L) g` to `polynomialCoefficientLinear φ f * g`. -/
  classical
  induction f using MvPolynomial.induction_on with
  | C c =>
    have hC : polynomialCoefficientLinear (σ := σ) φ (C c) = C (φ c) := by
      ext e; simp only [polynomialCoefficientLinear_coeff, coeff_C]; split_ifs <;> simp
    simp [hC]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    have hmul : polynomialCoefficientLinear φ (f * X j) = polynomialCoefficientLinear φ f * X j := by
      rw [show (X j : MvPolynomial σ K) = map (algebraMap k K) (X j) by simp]
      ext e
      rw [polynomialCoefficientLinear_coeff, coeff_mul, coeff_mul, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [coeff_map, polynomialCoefficientLinear_coeff]
      simpa only [Algebra.smul_def, smul_eq_mul, mul_comm, Algebra.algebraMap_self,
        RingHom.id_apply] using φ.map_smul ((X j : MvPolynomial σ k).coeff p.2) (f.coeff p.1)
    rw [hmul, map_mul, map_mul, eval_X, eval_X, hf, Function.comp_apply,
      mul_comm _ (algebraMap k K (x j)), ← Algebra.smul_def, φ.map_smul, smul_eq_mul, mul_comm]

/-- Linear coefficient descent: for a field extension `K / k`, a nonzero polynomial `f` over `K`
has a nonzero polynomial over `k` of total degree at most that of `f` vanishing at every
`k`-point where `f` vanishes. -/
theorem exists_nonzero_polynomial_linear_descent {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) :
    ∃ g : MvPolynomial (Fin n) k, g ≠ 0 ∧ g.totalDegree ≤ f.totalDegree ∧
      ∀ x : Fin n → k, eval (algebraMap k K ∘ x) f = 0 → eval x g = 0 := by
  /- Applying a linear map coefficientwise does not increase the total degree. -/
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hm
  refine ⟨polynomialCoefficientLinear φ f,
    fun he => hφ (by simpa [he] using (polynomialCoefficientLinear_coeff φ f m).symm),
    Finset.sup_le fun e he => le_totalDegree (mem_support_iff.mpr fun hz =>
      (mem_support_iff.mp he) (by rw [polynomialCoefficientLinear_coeff, hz, map_zero])),
    fun x hx => by rw [polynomialCoefficientLinear_eval, hx, map_zero]⟩

end
end CCDN
