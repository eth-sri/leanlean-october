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

/-- An absolutely irreducible integral polynomial has positive total degree. -/
lemma absolute_integer_polynomial_totalDegree_pos {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : AbsolutelyIrreducible f) :
    0 < f.totalDegree := by
  rw [← totalDegree_map_of_injective (Int.castRingHom (AlgebraicClosure ℚ)).injective_int f]
  exact totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit

/- The bad-prime factor of an integer polynomial `f` relative to a bad-reduction predicate
`P`: the product `primeSetFactor` of the primes `p > stepanovThreshold (deg f)` with `P f p`
when `f` is absolutely irreducible over `ℚ`, and `0` otherwise. The hypothesis `hP` gives the
finiteness of these primes for absolutely irreducible `f`. -/
/- The bad-prime factor `badPrimeFactor P hP f` is nonnegative. -/
/- The bad-prime factor of an integral polynomial that is not absolutely irreducible is
zero. -/
/- For an absolutely irreducible equation of degree `d`, the bad-prime factor is the
`primeSetFactor` of any finite set listing exactly the bad primes above `27 d⁴`. -/
/-- The geometric bad-prime factor: `badPrimeFactor` for `HypersurfaceBadReduction`, which
counts both failure of absolute irreducibility and degree loss modulo `p`. -/
def hypersurfaceBadPrimeFactor {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) : ℝ := by
  classical
  exact if h : AbsolutelyIrreducible f then
    primeSetFactor (finite_fin_hypersurface_bad_primes f h
      (absolute_integer_polynomial_totalDegree_pos f h)).toFinset
  else 0

/-- The geometric bad-prime factor `hypersurfaceBadPrimeFactor f` is nonnegative. -/
lemma hypersurfaceBadPrimeFactor_nonneg {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) :
    0 ≤ hypersurfaceBadPrimeFactor f := by
  unfold hypersurfaceBadPrimeFactor; split <;> positivity

/-- The geometric bad-prime factor of an integral polynomial that is not absolutely
irreducible is zero. -/
lemma hypersurfaceBadPrimeFactor_eq_zero {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : ¬ AbsolutelyIrreducible f) :
    hypersurfaceBadPrimeFactor f = 0 := by
  simp only [hypersurfaceBadPrimeFactor, dite_eq_right hf]

/-- For an absolutely irreducible integral polynomial of degree `d`, the geometric bad-prime
factor is the `primeSetFactor` of any finite set listing exactly the primes above
`stepanovThreshold d` at which `f` has geometric bad reduction. -/
lemma hypersurfaceBadPrimeFactor_eq_exp {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : AbsolutelyIrreducible f)
    (hdegree : f.totalDegree = d) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) :
    hypersurfaceBadPrimeFactor f = primeSetFactor bad := by
  classical
  unfold hypersurfaceBadPrimeFactor
  rw [dite_eq_left hf]
  congr 1; ext p
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hdegree, hbad]

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
    calc
      _ ≤ Real.exp (Real.log (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1) :=
        Real.exp_le_exp.mpr hcharge
      _ = _ := by
        rw [show Real.log (hypersurfaceHeightConstant (n + 1) *
            (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1 =
          Real.log (hypersurfaceHeightConstant (n + 1) *
            (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + (2 * mertensError + 1) by ring,
          Real.exp_add, Real.exp_log (by positivity)]
        ring
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf]
    positivity

end
end CCDN
