/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.ForMathlib.MvPolynomial

/-! Bad-prime factors of integer polynomials, and the geometric bad-prime factor used by the
determinant method. For nonzero homogeneous equations the geometric
factor agrees with CCDN Definition 3.2.1. For affine equations its bad-prime predicate also
includes degree loss; this stronger convention is not identical to the literal printed
definition. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An absolutely irreducible integral polynomial has positive total degree. -/
lemma absolute_integer_polynomial_totalDegree_pos {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : AbsolutelyIrreducible f) :
    0 < f.totalDegree := by
  rw [← totalDegree_map_of_injective (Int.castRingHom (AlgebraicClosure ℚ)).injective_int f]
  exact totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit

/-- The exact finite set of geometric bad primes above the cutoff. -/
def geometricBadPrimes {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : AbsolutelyIrreducible f) : Finset ℕ :=
  (finite_fin_hypersurface_bad_primes f hf (absolute_integer_polynomial_totalDegree_pos f hf)).toFinset

@[simp] private lemma mem_geometricBadPrimes {n p : ℕ} {f : MvPolynomial (Fin (n + 1)) ℤ}
    (hf : AbsolutelyIrreducible f) : p ∈ geometricBadPrimes f hf ↔
      stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p := by
  simp [geometricBadPrimes]

/-- The factor is the prime product for absolute equations, and zero otherwise. -/
def hypersurfaceBadPrimeFactor {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) : ℝ := by
  classical
  exact if hf : AbsolutelyIrreducible f then primeSetFactor (geometricBadPrimes f hf) else 0

section

variable {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
include n f

lemma hypersurfaceBadPrimeFactor_nonneg :
    0 ≤ hypersurfaceBadPrimeFactor f := by
  unfold hypersurfaceBadPrimeFactor
  split <;> positivity

lemma hypersurfaceBadPrimeFactor_eq_zero
    (hf : ¬ AbsolutelyIrreducible f) : hypersurfaceBadPrimeFactor f = 0 := by
  simp [hypersurfaceBadPrimeFactor, hf]

end

lemma hypersurfaceBadPrimeFactor_eq_exp {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : AbsolutelyIrreducible f) (hdegree : f.totalDegree = d) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) :
    hypersurfaceBadPrimeFactor f = primeSetFactor bad := by
  rw [hypersurfaceBadPrimeFactor, dite_eq_left hf]
  congr 1
  ext p
  rw [mem_geometricBadPrimes, hbad, hdegree]

section

variable {n m : ℕ}
  (f : MvPolynomial (Fin (n + 1)) ℤ) (g : MvPolynomial (Fin (m + 1)) ℤ)
include n m f g

/-- Extra primes multiply the factor by at most `exp` of their number. -/
theorem hypersurfaceBadPrimeFactor_le_of_badReduction_imp (E : Finset ℕ)
    (hd : f.totalDegree = g.totalDegree)
    (habs : AbsolutelyIrreducible f → AbsolutelyIrreducible g)
    (hbad : ∀ q, q ∉ E → HypersurfaceBadReduction f q → HypersurfaceBadReduction g q) :
    hypersurfaceBadPrimeFactor f ≤ Real.exp (E.card : ℝ) * hypersurfaceBadPrimeFactor g := by
  classical
  by_cases hf : AbsolutelyIrreducible f
  · have hg := habs hf
    rw [hypersurfaceBadPrimeFactor, dite_eq_left hf, hypersurfaceBadPrimeFactor, dite_eq_left hg,
      ← Real.exp_add, Real.exp_le_exp]
    let w (p : ℕ) : ℝ := Real.log p / p
    have hw (p : ℕ) : 0 ≤ w p := by dsimp [w]; positivity
    have hw' (p : ℕ) : w p ≤ 1 :=
      div_le_one_of_le₀ (Real.log_le_self (by positivity)) (by positivity)
    have hs : geometricBadPrimes f hf ⊆ E ∪ geometricBadPrimes g hg := by
      grind [mem_geometricBadPrimes]
    calc
      ∑ p ∈ geometricBadPrimes f hf, w p ≤ ∑ p ∈ E ∪ geometricBadPrimes g hg, w p :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => hw p)
      _ ≤ (∑ p ∈ E, w p) + ∑ p ∈ geometricBadPrimes g hg, w p :=
        by
          have hh := Finset.sum_union_inter (s₁ := E) (s₂ := geometricBadPrimes g hg) (f := w)
          linarith [Finset.sum_nonneg (s := E ∩ geometricBadPrimes g hg) (fun p _ => hw p)]
      _ ≤ _ := by
        have hsum : (∑ p ∈ E, w p) ≤ (E.card : ℝ) := by
          simpa using Finset.sum_le_sum (s := E) (fun p _ => hw' p)
        linarith
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf]
    exact mul_nonneg (Real.exp_pos _).le (hypersurfaceBadPrimeFactor_nonneg g)

/-- Inclusion of the geometric bad-prime sets gives monotonicity of
 the corresponding factors, even across different numbers of variables. -/
theorem hypersurfaceBadPrimeFactor_mono_of_badReduction_imp
    (hd : f.totalDegree = g.totalDegree)
    (habs : AbsolutelyIrreducible f → AbsolutelyIrreducible g)
    (hbad : ∀ q, HypersurfaceBadReduction f q → HypersurfaceBadReduction g q) :
    hypersurfaceBadPrimeFactor f ≤ hypersurfaceBadPrimeFactor g := by
  simpa using hypersurfaceBadPrimeFactor_le_of_badReduction_imp f g ∅ hd habs
    (fun q _ => hbad q)

end

/-- The bad-prime factor satisfies the coefficient-height bound also
for nonabsolute equations, where the factor is zero by definition. -/
theorem hypersurfaceBadPrimeFactor_le_height {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    hypersurfaceBadPrimeFactor f ≤
      (Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2) := by
  have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
  have hc : 0 < hypersurfaceHeightConstant (n + 1) :=
    zero_lt_one.trans_le (hypersurfaceHeightConstant_one_le _)
  by_cases hf : AbsolutelyIrreducible f
  · obtain ⟨bad, hbad, hcharge⟩ := exists_fin_hypersurface_bad_prime_charge f hf
      (absolute_integer_polynomial_totalDegree_pos f hf) H hH hcoeff
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl bad hbad]
    refine (Real.exp_le_exp.mpr hcharge).trans_eq ?_
    rw [add_assoc, Real.exp_add, Real.exp_log (by positivity)]
    ring
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf]
    positivity

end
end CCDN
