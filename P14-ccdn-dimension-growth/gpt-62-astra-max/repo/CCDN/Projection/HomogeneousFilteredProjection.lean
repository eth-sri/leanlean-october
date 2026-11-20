/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.Algebra.MvPolynomial.Monad

/-! A linear homogeneous projection of a homogeneous quotient is strict
for the total-degree filtration: any image element of bounded degree has a
preimage of the same bounded degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K σ τ : Type*} [Field K] (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (N : ℕ) (p : MvPolynomial σ K)

include ha in
/-- Substituting homogeneous linear forms commutes with taking homogeneous components: the
degree-`N` component of `aeval a p` is `aeval a` of the degree-`N` component of `p`. -/
lemma homogeneousComponent_aeval_linear :
    homogeneousComponent N (aeval a p) = aeval a (homogeneousComponent N p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp_all
  | monomial e c =>
    have hm := isHomogeneous_monomial c (rfl : e.degree = e.degree)
    have hm'  := by
      simpa only [one_mul] using hm.aeval a ha
    rw [homogeneousComponent_of_mem hm, homogeneousComponent_of_mem hm']
    split_ifs <;> simp

end
end CCDN
