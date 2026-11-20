/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.ForMathlib.MvPolynomial

/-! Bad-prime factors of integer polynomials, and the geometric bad-prime factor used by the
determinant method. A bad-prime factor `badPrimeFactor P` is zero for nonabsolute equations
and the exact finite exponential product over the primes above `stepanovThreshold` satisfying
the bad-reduction predicate `P` otherwise. For nonzero homogeneous equations the geometric
factor agrees with CCDN Definition 3.2.1. For affine equations its bad-prime predicate also
includes degree loss; this stronger convention is not identical to the literal printed
definition. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {n : ℕ} (f : IntegerPolynomial (n+1)) (hf : AbsolutelyIrreducible f)

/-- An absolutely irreducible integral polynomial has positive total degree. -/
lemma absolute_integer_polynomial_totalDegree_pos
    (f : IntegerPolynomial (n + 1))
    (hf : AbsolutelyIrreducible f) :
    0 < f.totalDegree := by
  rw [← totalDegree_map_of_injective (Int.castRingHom (AlgebraicClosure ℚ)).injective_int f]
  exact totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit

/-- The primes that must be omitted in the good-reduction estimate. -/
def largeBadPrimes :=
  (finite_fin_hypersurface_bad_primes f hf (absolute_integer_polynomial_totalDegree_pos f hf)).toFinset

@[simp] theorem mem_largeBadPrimes (p : ℕ) :
    p ∈ largeBadPrimes f hf ↔ stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p := Set.Finite.mem_toFinset _

def hypersurfaceBadPrimeFactor : ℝ := by
  classical exact if hf : AbsolutelyIrreducible f then primeSetFactor (largeBadPrimes f hf) else 0

end

variable {n d : ℕ} (f : IntegerPolynomial (n + 1))

/-- The geometric bad-prime factor `hypersurfaceBadPrimeFactor f` is nonnegative. -/
lemma hypersurfaceBadPrimeFactor_nonneg :
    0 ≤ hypersurfaceBadPrimeFactor f :=
by
  unfold hypersurfaceBadPrimeFactor
  split <;> positivity

/-- The geometric bad-prime factor of an integral polynomial that is not absolutely
irreducible is zero. -/
lemma hypersurfaceBadPrimeFactor_eq_zero
    (hf : ¬ AbsolutelyIrreducible f) :
    hypersurfaceBadPrimeFactor f = 0 :=
by simp [hypersurfaceBadPrimeFactor, hf]

/-- For an absolutely irreducible integral polynomial of degree `d`, the geometric bad-prime
factor is the `primeSetFactor` of any finite set listing exactly the primes above
`stepanovThreshold d` at which `f` has geometric bad reduction. -/
lemma hypersurfaceBadPrimeFactor_eq_exp
    (hf : AbsolutelyIrreducible f)
    (hdegree : f.totalDegree = d) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) :
    hypersurfaceBadPrimeFactor f = primeSetFactor bad :=
by
  classical
  simp only [hypersurfaceBadPrimeFactor, dite_eq_left hf]
  congr 1
  aesop

/-- The bad-prime factor satisfies the coefficient-height bound also
for nonabsolute equations, where the factor is zero by definition. -/
theorem hypersurfaceBadPrimeFactor_le_height (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    hypersurfaceBadPrimeFactor f ≤
      (Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1)) *
        (1 + Real.log H / (f.totalDegree : ℝ) ^ 2) := by
  have hlog := Real.log_nonneg hH
  have hc : 0 < hypersurfaceHeightConstant (n + 1) :=
    zero_lt_one.trans_le (hypersurfaceHeightConstant_one_le _)
  by_cases hf : AbsolutelyIrreducible f
  · obtain ⟨bad, hbad, hcharge⟩ := exists_fin_hypersurface_bad_prime_charge f hf
      (absolute_integer_polynomial_totalDegree_pos f hf) H hH hcoeff
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl bad hbad]
    calc
      _ ≤ Real.exp _ :=
        Real.exp_le_exp.mpr hcharge
      _ = _ := by
        rw [show Real.log _ + 2 * mertensError + 1 =
          Real.log _ + (2 * mertensError + 1) by ring,
          Real.exp_add, Real.exp_log (by positivity)]
        ring
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf]
    positivity

end
end CCDN
