/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Polynomial.Basic

/-! Homogeneity in the coefficient variables, while retaining independent
polynomial parameters. This property survives determinant expansion and
extraction of any parameter coefficient. -/

@[expose] public section
namespace CCDN
open MvPolynomial

/-- A polynomial `f` in the variables `σ` with coefficients in `MvPolynomial τ R` is coefficientwise
homogeneous of degree `d` if each of its coefficients is a homogeneous polynomial of degree `d` in
the variables `τ`. -/
noncomputable def CoefficientwiseHomogeneous {R σ τ : Type*} [CommRing R]
    (f : MvPolynomial σ (MvPolynomial τ R)) (d : ℕ)  :=
  ∀ m, (f.coeff m).IsHomogeneous d

namespace CoefficientwiseHomogeneous

variable {R σ τ : Type*} [CommRing R]



/-- The negation of a coefficientwise homogeneous polynomial of degree `d` is coefficientwise
homogeneous of degree `d`. -/
lemma neg {f : MvPolynomial σ (MvPolynomial τ R)} {d : ℕ}
    (hf : CoefficientwiseHomogeneous f d) :
    CoefficientwiseHomogeneous (-f) d := by
  intro m
  rw [coeff_neg]
  exact (hf m).neg

variable {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial τ R))

/-- A finite sum of coefficientwise homogeneous polynomials of degree `d` is coefficientwise
homogeneous of degree `d`. -/
lemma sum  (d : ℕ)
    (hf : ∀ i ∈ s, CoefficientwiseHomogeneous (f i) d) :
    CoefficientwiseHomogeneous (∑ i ∈ s, f i) d := by
  intro m
  rw [coeff_sum]
  exact IsHomogeneous.sum s _ d (fun i hi => hf i hi m)

/-- The product of coefficientwise homogeneous polynomials of degrees `d` and `e` is coefficientwise
homogeneous of degree `d + e`. -/
lemma mul {f g : MvPolynomial σ (MvPolynomial τ R)} {d e : ℕ}
    (hf : CoefficientwiseHomogeneous f d) (hg : CoefficientwiseHomogeneous g e) :
    CoefficientwiseHomogeneous (f * g) (d + e) := by
  classical
  intro m
  rw [coeff_mul]
  exact IsHomogeneous.sum _ _ _ (fun ij _ => (hf ij.1).mul (hg ij.2))

/-- The constant polynomial `C f` is coefficientwise homogeneous of degree `d` when `f` is a
homogeneous polynomial of degree `d` in the variables `τ`. -/
lemma C_of_isHomogeneous {f : MvPolynomial τ R} {d : ℕ} (hf : f.IsHomogeneous d) :
    CoefficientwiseHomogeneous (MvPolynomial.C f : MvPolynomial σ (MvPolynomial τ R)) d := by
  classical
  intro m
  rw [coeff_C]
  split_ifs
  · exact hf
  · exact isHomogeneous_zero τ R d

/-- The polynomial `1` is coefficientwise homogeneous of degree `0`. -/
lemma one : CoefficientwiseHomogeneous (1 : MvPolynomial σ (MvPolynomial τ R)) 0 := by
  solve_by_elim [map_one, C_of_isHomogeneous, isHomogeneous_one]

/-- A polynomial over `R`, with its coefficients viewed as constants of `MvPolynomial τ R`, is
coefficientwise homogeneous of degree `0`. -/
lemma map_C (f : MvPolynomial σ R) :
    CoefficientwiseHomogeneous
      (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) f) 0 := by
  solve_by_elim [coeff_map, isHomogeneous_C]

/-- A finite product of coefficientwise homogeneous polynomials of degrees `d i` is coefficientwise
homogeneous of degree `∑ i ∈ s, d i`. -/
lemma prod 
    (d : ι → ℕ) (hf : ∀ i ∈ s, CoefficientwiseHomogeneous (f i) (d i)) :
    CoefficientwiseHomogeneous (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp_all [Finset.prod_empty, Finset.sum_empty, one]
  | @insert a s ha ih =>
    simp_all [Finset.prod_insert, Finset.sum_insert,  mul]

/-- The determinant of an `r × r` matrix whose entries are coefficientwise homogeneous of degree `1`
is coefficientwise homogeneous of degree `r`. -/
lemma det {r : ℕ} (M : Matrix (Fin r) (Fin r) (MvPolynomial σ (MvPolynomial τ R)))
    (hM : ∀ i j, CoefficientwiseHomogeneous (M i j) 1) :
    CoefficientwiseHomogeneous M.det r := by
  classical
  rw [Matrix.det_apply']
  apply sum
  intro π _
  have hp := prod Finset.univ (fun i => M (π i) i) (fun _ => 1) (fun i _ => hM _ i)
  have hp' : CoefficientwiseHomogeneous (∏ i, M (π i) i) r := by
    simp_all
  have hc : CoefficientwiseHomogeneous
      (MvPolynomial.C (MvPolynomial.C ((Equiv.Perm.sign π : ℤ) : R)) :
        MvPolynomial σ (MvPolynomial τ R)) 0 :=
    C_of_isHomogeneous (isHomogeneous_C τ _)
  have hh := hc.mul hp'
  simpa only [zero_add, map_intCast] using hh

end CoefficientwiseHomogeneous
end CCDN
