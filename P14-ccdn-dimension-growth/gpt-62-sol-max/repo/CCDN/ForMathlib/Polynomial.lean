/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Finite differences, derivatives and resultants of univariate polynomials

## Main results

* `Polynomial.derivative_ne_zero_of_natCast_natDegree_ne_zero`: a polynomial whose degree is
  nonzero in the coefficient ring has nonzero derivative.
* `Matrix.natDegree_det_le`, `Polynomial.natDegree_resultant_le`: degree bounds for determinants
  and Sylvester resultants of polynomials in a coefficient parameter, independent of the
  eliminated variable.
* `Polynomial.resultant_ne_zero_of_irreducible_of_natDegree_lt`: padding the second Sylvester
  degree preserves nonvanishing when the first polynomial is irreducible.
-/

@[expose] public section

namespace Polynomial

/-- A polynomial whose degree `n` satisfies `(n : R) ≠ 0` has nonzero derivative. -/
theorem derivative_ne_zero_of_natCast_natDegree_ne_zero {R : Type*} [Semiring R]
    [NoZeroDivisors R] {f : R[X]} (hn : (f.natDegree : R) ≠ 0) : derivative f ≠ 0 := by
  have hpos : 0 < f.natDegree := by
    rw [Nat.pos_iff_ne_zero]
    rintro h
    simp [h] at hn
  
  intro hz
  have hc := congrArg (fun g : R[X] => g.coeff (f.natDegree - 1)) hz
  rw [coeff_derivative, show f.natDegree - 1 + 1 = f.natDegree by omega, coeff_zero] at hc
  have he : ((f.natDegree - 1 : ℕ) : R) + 1 = (f.natDegree : R) := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hpos]
  simp_all

end Polynomial

namespace Matrix

open Polynomial

/-- The degree of a determinant of polynomials is at most the size times an entrywise degree
bound. -/
theorem natDegree_det_le {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R[X]) (D : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ D) :
    M.det.natDegree ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : ι, D := Finset.sum_le_sum fun i _ => hM (σ i) i
    _ = _ := by simp

end Matrix

namespace Polynomial

/-- The degree in the coefficient parameter of a Sylvester resultant is at most the Sylvester
size times a coefficientwise degree bound. -/
theorem natDegree_resultant_le {R : Type*} [CommRing R]
    (f g : R[X][X]) (m n D : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (f.resultant g m n).natDegree ≤ (m + n) * D := by
  have hM : ∀ i j, (f.sylvester g m n i j).natDegree ≤ D := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      aesop
    | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      aesop
  simpa [Fintype.card_fin, resultant] using Matrix.natDegree_det_le (f.sylvester g m n) D hM

/-- Padding the second Sylvester degree preserves nonvanishing when the
first polynomial is irreducible and the second is nonzero of smaller degree. -/
theorem resultant_ne_zero_of_irreducible_of_natDegree_lt
    {K : Type*} [Field K] (f g : K[X]) (hf : Irreducible f) (hg : g ≠ 0)
    (hdeg : g.natDegree < f.natDegree) (n : ℕ) (hn : g.natDegree ≤ n) :
    f.resultant g f.natDegree n ≠ 0 := by
  have hcop := hf.coprime_iff_not_dvd.mpr fun h =>
    (not_le_of_gt hdeg) (natDegree_le_of_dvd h hg)
  have he : n = g.natDegree + (n - g.natDegree) := by omega
  rw [he, resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf.ne_zero))
    (resultant_ne_zero f g hcop)

end Polynomial
