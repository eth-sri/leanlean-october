/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/- A polynomial outside a prime hypersurface ideal is nonzero at some point
of that hypersurface over an algebraically closed field. -/

/-- An irreducible hypersurface of positive degree smaller than the characteristic (or in
characteristic zero) has a smooth rational point over the algebraically closed base. -/
theorem exists_smooth_hypersurface_point_of_degree_lt_char
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial σ K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K f.totalDegree) :
    ∃ (z : σ → K) (j : σ), eval z f = 0 ∧ eval z (pderiv j f) ≠ 0 := by
  /- A nonzero partial derivative of an irreducible polynomial is nonzero at
  some point on its hypersurface. -/
  classical
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hpos hchar
  have hnd : ¬ f ∣ pderiv j f := by
    rintro ⟨q, he⟩
    have hq : q ≠ 0 := fun hq => hj (by rw [he, hq, mul_zero])
    have hd := totalDegree_mul_of_isDomain hf.ne_zero hq
    have hp := pderiv_totalDegree_le f j
    rw [← he] at hd; omega
  let I : Ideal (MvPolynomial σ K) := Ideal.span {f}
  have : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  by_contra! h
  refine hnd (Ideal.mem_span_singleton.mp ?_)
  change pderiv j f ∈ I
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
  exact fun z hz => h z j (hz f (Ideal.subset_span (Set.mem_singleton f)))

end
end CCDN
