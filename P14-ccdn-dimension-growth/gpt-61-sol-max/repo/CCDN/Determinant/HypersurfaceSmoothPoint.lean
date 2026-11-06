/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Algebra.CharZeroOrGT
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CCDN.Determinant.PlaneSingularities
import CCDN.ForMathlib.MvPolynomialDerivative
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Nullstellensatz

/-! Smooth points on irreducible hypersurfaces over an algebraically
closed field. The characteristic bound supplies a nonzero partial derivative;
the Nullstellensatz supplies a point where it does not vanish. -/

public section
namespace CCDN
open MvPolynomial

variable {K σ : Type*} [Field K] [IsAlgClosed K]

/-- A polynomial outside a prime hypersurface ideal is nonzero at some point
of that hypersurface over an algebraically closed field. -/
theorem exists_hypersurface_point_eval_ne_zero
     [Finite σ]
    (f g : MvPolynomial σ K) (hf : Irreducible f) (hg : ¬ f ∣ g) :
    ∃ z : σ → K, eval z f = 0 ∧ eval z g ≠ 0 := by
  classical
  let I := Ideal.span {f}
  have : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  by_contra! h
  apply hg
  apply Ideal.mem_span_singleton.mp
  change g ∈ I
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
  intro z hz
  apply h z
  exact hz f (Ideal.subset_span (Set.mem_singleton f))


/-- An irreducible hypersurface of positive degree smaller than the characteristic (or in
characteristic zero) has a smooth rational point over the algebraically closed base. -/
theorem exists_smooth_hypersurface_point_of_degree_lt_char
     [Fintype σ]
    (f : MvPolynomial σ K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K f.totalDegree) :
    ∃ (z : σ → K) (j : σ), eval z f = 0 ∧ eval z (pderiv j f) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hpos hchar
  obtain ⟨z, hz, hderiv⟩ := (show ∃ z, (eval z) f = (0 : K) ∧ (eval z) ((pderiv j) f) ≠ (0 : K) from (by
                              apply exists_hypersurface_point_eval_ne_zero f (pderiv j f) hf
                              rintro ⟨q, he⟩
                              have hq : q ≠ 0 := by
                                simp_all
                              have hd := totalDegree_mul_of_isDomain hf.ne_zero hq
                              rw [← he] at hd
                              have hp := pderiv_totalDegree_le f j
                              omega))
  exact ⟨z, j, hz, hderiv⟩

end CCDN
