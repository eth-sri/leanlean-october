/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.BivariateTotalDegree

/-! A bounded integer direction where the highest homogeneous part does not
vanish. The direction polynomial packages the top-degree coefficients. -/

namespace CCDN
noncomputable section
open Polynomial

section
variable {R : Type*} [CommRing R] (f : R[X][X])

/-- Highest homogeneous part, evaluated at outer coordinate one and inner
coordinate the polynomial variable. -/
def leadingDirectionPolynomial (d : ℕ) : R[X] :=
  ∑ j ∈ Finset.range (d + 1), monomial j ((f.coeff (d - j)).coeff j)

/-- The `j`-th coefficient of the leading direction polynomial of degree `d` is the coefficient of
`f` with outer exponent `d - j` and inner exponent `j` when `j ≤ d`, and zero otherwise. -/
lemma leadingDirectionPolynomial_coeff
    (d j : ℕ) :
    (leadingDirectionPolynomial f d).coeff j =
      if j ≤ d then (f.coeff (d - j)).coeff j else 0 := by
  simp [leadingDirectionPolynomial, coeff_monomial]

lemma leadingDirectionPolynomial_natDegree_le
    (d : ℕ) : (leadingDirectionPolynomial f d).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (by grind)

lemma leadingDirectionPolynomial_ne_zero
    (hf : f ≠ 0) :
    leadingDirectionPolynomial f (bivariateTotalDegree f) ≠ 0 := by
  obtain ⟨i, j, hdeg, hc⟩ : ∃ i j : ℕ, i + j = bivariateTotalDegree f ∧ (f.coeff i).coeff j ≠ 0 := by
    let g := (bivariatePolynomialEquiv R).symm f
    have hg : g ≠ 0 := (map_ne_zero_iff _ (bivariatePolynomialEquiv R).symm.injective).mpr hf
    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup g.support (by simp_all) (fun s => s.sum (fun _ e => e))
    refine ⟨m 0, m 1, ?_, ?_⟩
    · change _ = g.support.sup (fun s => s.sum (fun _ e => e))
      rw [hmax]
      conv_rhs => rw [bivariate_exponent_eq m]
      exact (bivariate_exponent_sum _ _).symm
    · have hc := bivariatePolynomialEquiv_coeff g (m 0) (m 1)
      rw [AlgEquiv.apply_symm_apply, ← bivariate_exponent_eq m] at hc
      grind
  intro hz
  have hh := congrArg (fun q => q.coeff j) hz
  rw [leadingDirectionPolynomial_coeff, ite_eq_left (by omega), coeff_zero] at hh
  have he : bivariateTotalDegree f - j = i := by omega
  exact hc (he ▸ hh)

end

