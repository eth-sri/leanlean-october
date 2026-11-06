/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateTotalDegree

/-! A bounded integer direction where the highest homogeneous part does not
vanish. The direction polynomial packages the top-degree coefficients. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- Highest homogeneous part, evaluated at outer coordinate one and inner
coordinate the polynomial variable. -/
def leadingDirectionPolynomial {R : Type*} [CommRing R] (f : R[X][X]) (d : ℕ) : R[X] :=
  ∑ j ∈ Finset.range (d + 1), monomial j ((f.coeff (d - j)).coeff j)

/-- The `j`-th coefficient of the leading direction polynomial of degree `d` is the coefficient of
`f` with outer exponent `d - j` and inner exponent `j` when `j ≤ d`, and zero otherwise. -/
lemma leadingDirectionPolynomial_coeff {R : Type*} [CommRing R]
    (f : R[X][X]) (d j : ℕ) :
    (leadingDirectionPolynomial f d).coeff j =
      if j ≤ d then (f.coeff (d - j)).coeff j else 0 := by
  classical
  simp [leadingDirectionPolynomial, coeff_monomial]

/-- Among 0,...,d, at least one integer parameter gives a nonvanishing leading
direction. The proof uses only the univariate root bound. -/
theorem exists_bounded_leading_direction (f : ℤ[X][X]) (hf : f ≠ 0) :
    ∃ a : ℕ, a ≤ bivariateTotalDegree f ∧
      (leadingDirectionPolynomial f (bivariateTotalDegree f)).eval (a : ℤ) ≠ 0 := by
  let d := bivariateTotalDegree f
  let q := leadingDirectionPolynomial f d
  let g := (bivariatePolynomialEquiv ℤ).symm f
  have hg : g ≠ 0 := (map_ne_zero_iff _ (bivariatePolynomialEquiv ℤ).symm.injective).mpr hf
  have hs : g.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h => hg (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup g.support hs (fun s => s.sum (fun _ e => e))
  have hdeg : m 0 + m 1 = d := by
    change _ = g.support.sup (fun s => s.sum (fun _ e => e))
    rw [hmax]
    conv_rhs => rw [bivariate_exponent_eq m]
    exact (bivariate_exponent_sum _ _).symm
  have hc : (f.coeff (m 0)).coeff (m 1) ≠ 0 := by
    have hc' := bivariatePolynomialEquiv_coeff g (m 0) (m 1)
    change ((bivariatePolynomialEquiv ℤ ((bivariatePolynomialEquiv ℤ).symm f)).coeff (m 0)).coeff
      (m 1) = _ at hc'
    rw [AlgEquiv.apply_symm_apply, ← bivariate_exponent_eq m] at hc'
    exact hc'.symm ▸ MvPolynomial.mem_support_iff.mp hm
  have hq0 : q ≠ 0 := fun hz => by
    have hh := congrArg (fun p : ℤ[X] => p.coeff (m 1)) hz
    rw [leadingDirectionPolynomial_coeff, ite_eq_left (by omega), coeff_zero] at hh
    exact hc (show d - m 1 = m 0 by omega ▸ hh)
  by_contra! hn
  refine hq0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero (ι := Fin (d + 1))
    (f := fun i => (i.val : ℤ)) q (fun i j h => Fin.ext (Int.ofNat_inj.mp h))
    (fun i => hn i.val (by omega)) ?_)
  have h : q.natDegree ≤ d := natDegree_sum_le_of_forall_le _ _ fun j hj =>
    (natDegree_monomial_le _).trans (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)
  simpa only [Fintype.card_fin] using Nat.lt_succ_of_le h

end
end CCDN
