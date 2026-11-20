/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateCoefficientMatrix
public import Mathlib.LinearAlgebra.Matrix.Rank
import CCDN.Noether.BivariateFactorForms

/-!
The closed-form coefficient matrix commutes with coefficient ring maps,
including passage from integers to characteristic zero and reduction modulo p.

Reconstruct bounded polynomial closed forms inside the matrix
kernel. Two independent forms force the rank drop used by the integer minor.
-/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- Apply a ring map to both levels of bivariate coefficients. -/
def bivariateMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    R[X][X] →+* S[X][X] := Polynomial.mapRingHom (Polynomial.mapRingHom φ)

section

variable {R S : Type*} [CommRing R] [CommRing S]
  (φ : R →+* S)
include R S φ

/-- The coefficients of `bivariateMap φ f` are the images under `φ` of those of `f`. -/
@[simp]
lemma bivariateMap_coeff (f : R[X][X]) (i j : ℕ) :
    ((bivariateMap φ f).coeff i).coeff j = φ ((f.coeff i).coeff j) := by
  simp [bivariateMap]

/-- Matrix entries base-change exactly; no injectivity or characteristic
hypothesis on the coefficient map is needed. -/
theorem closedFormCoefficientMatrix_map (d : ℕ) (f : R[X][X]) :
    (closedFormCoefficientMatrix d f).map φ =
      closedFormCoefficientMatrix d (bivariateMap φ f) := by
  ext i j
  rcases j with j | j <;> simp only [Matrix.map_apply, closedFormCoefficientMatrix_inl,
    closedFormCoefficientMatrix_inr] <;> split_ifs <;> simp

end

end
end CCDN

namespace CCDN
noncomputable section
open Polynomial Matrix

/-- All coefficients outside the strict rectangular grid vanish. -/
def InBivariateGrid {R : Type*} [CommRing R] (d : ℕ) (f : R[X][X]) : Prop :=
  ∀ i j, d ≤ i ∨ d ≤ j → (f.coeff i).coeff j = 0

section

variable {R : Type*} [CommRing R] (d : ℕ)
include R d

/-- The polynomial with coefficients on the grid `BivariateGrid d` has zero coefficient at every
monomial with outer exponent `i` and inner exponent `j` such that `d ≤ i` or `d ≤ j`. -/
lemma bivariateGridPolynomial_coeff_zero
    (v : BivariateGrid d → R) (i j : ℕ) (h : d ≤ i ∨ d ≤ j) :
    ((bivariateGridPolynomial R d v).coeff i).coeff j = 0 := by
  classical
  simp only [bivariateGridPolynomial, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k _
  simp only [coeff_monomial]
  split_ifs with he
  · rw [coeff_monomial, ite_eq_right]
    
    
    omega
  · simp

/-- Coefficient extraction followed by decoding recovers every polynomial
supported on the grid. -/
theorem bivariateGridPolynomial_reconstruct (f : R[X][X]) (hf : InBivariateGrid d f) :
    bivariateGridPolynomial R d (fun i => (f.coeff i.1.val).coeff i.2.val) = f := by
  ext i j
  by_cases hi : i < d
  · by_cases hj : j < d
    · exact bivariateGridPolynomial_coeff _ ⟨i, hi⟩ ⟨j, hj⟩
    · rw [bivariateGridPolynomial_coeff_zero d _ i j (Or.inr (by omega)),
        hf i j (Or.inr (by omega))]
  · rw [bivariateGridPolynomial_coeff_zero d _ i j (Or.inl (by omega)), hf i j (Or.inl (by omega))]

/-- Every pair supported on the grid comes from a coefficient vector. -/
private theorem exists_closedFormPair_of_grid (u : R[X][X] × R[X][X]) (hp : InBivariateGrid d u.1)
    (hq : InBivariateGrid d u.2) :
    ∃ v, closedFormPair R d v = u := by
  refine ⟨Sum.elim (fun i => (u.1.coeff i.1.val).coeff i.2.val)
    (fun i => (u.2.coeff i.1.val).coeff i.2.val), ?_⟩
  exact Prod.ext (bivariateGridPolynomial_reconstruct d u.1 hp)
    (bivariateGridPolynomial_reconstruct d u.2 hq)

end

/-- The gradient itself satisfies the closed-form equation in every field. -/
lemma closedFormOperator_gradient {F : Type*} [Field F] (f : F[X][X]) :
    closedFormOperator f (f.derivative, (bivariateCoefficientDerivative F) f) = 0 := by
  change (bivariateCoefficientDerivative F) f.derivative * f -
    f.derivative * (bivariateCoefficientDerivative F) f -
    ((bivariateCoefficientDerivative F) f).derivative * f +
    (bivariateCoefficientDerivative F) f * f.derivative = 0
  rw [derivative_bivariateCoefficientDerivative]
  ring

/-- Rank and nullity account for all `2*d²` unknown coefficients. -/
lemma closedForm_rank_add_nullity {F : Type*} [Field F] (d : ℕ) (f : F[X][X]) :
    (closedFormCoefficientMatrix d f).rank +
      Module.finrank F (closedFormCoefficientMatrix d f).mulVecLin.ker = 2 * d ^ 2 := by
  have h := (closedFormCoefficientMatrix d f).mulVecLin.finrank_range_add_finrank_ker
  change (closedFormCoefficientMatrix d f).rank + _ = _ at h
  simpa [ClosedFormColumns, BivariateGrid, pow_two, two_mul] using h

/-- Two polynomial solutions, one not a scalar multiple of the other, give
a rank drop of at least two. -/
theorem closedForm_rank_drop_of_two_forms {F : Type*} [Field F]
    (d : ℕ) (f : F[X][X]) (u w : F[X][X] × F[X][X])
    (hu₁ : InBivariateGrid d u.1) (hu₂ : InBivariateGrid d u.2)
    (hw₁ : InBivariateGrid d w.1) (hw₂ : InBivariateGrid d w.2)
    (hu : closedFormOperator f u = 0) (hw : closedFormOperator f w = 0)
    (hu0 : u ≠ 0) (hind : ∀ a : F, a • u ≠ w) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  obtain ⟨v, hv⟩ := exists_closedFormPair_of_grid d u hu₁ hu₂
  obtain ⟨z, hz⟩ := exists_closedFormPair_of_grid d w hw₁ hw₂
  let V := (closedFormCoefficientMatrix d f).mulVecLin.ker
  have hvk : v ∈ V := by
    apply (closedFormCoefficientMatrix_kernel d f v).mpr
    rw [hv, hu]
  have hzk : z ∈ V := by
    apply (closedFormCoefficientMatrix_kernel d f z).mpr
    rw [hz, hw]
  let v' : V := ⟨v, hvk⟩
  let z' : V := ⟨z, hzk⟩
  have hv0 : v' ≠ 0 := by
    intro hh
    have hh' : v = 0 := congrArg Subtype.val hh
    apply hu0
    rw [← hv, hh', map_zero]
  have hi : LinearIndependent F ![v', z'] := by
    rw [LinearIndependent.pair_iff' hv0]
    intro a ha
    apply hind a
    have hh : a • v = z := congrArg Subtype.val ha
    rw [← hv, ← hz, ← (closedFormPair F d).map_smul, hh]
  have hdim : 2 ≤ Module.finrank F V := by simpa using hi.fintype_card_le_finrank
  change 2 ≤ Module.finrank F (closedFormCoefficientMatrix d f).mulVecLin.ker at hdim
  have := closedForm_rank_add_nullity d f
  omega

end
end CCDN
