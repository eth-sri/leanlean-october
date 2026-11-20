/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Noether.ClosedFormEntry
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

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (f : R[X][X])

/-- Apply a ring map to both levels of bivariate coefficients. -/
def bivariateMap :
    R[X][X] →+* S[X][X] := Polynomial.mapRingHom (Polynomial.mapRingHom φ)

/-- The coefficients of `bivariateMap φ f` are the images under `φ` of those of `f`. -/
@[simp]
lemma bivariateMap_coeff (i j : ℕ) :
    ((bivariateMap φ f).coeff i).coeff j = φ ((f.coeff i).coeff j) := by
  simp [bivariateMap]

/-- Each column's integer stencil commutes with extension of coefficients. -/
theorem closedFormCoefficientMatrix_map : (closedFormCoefficientMatrix d f).map φ =
    closedFormCoefficientMatrix d (bivariateMap φ f) := by
  ext i j; simp [closedFormEntry_apply]

end
end CCDN

namespace CCDN
noncomputable section
open Polynomial Matrix

section

variable {R : Type*} [CommRing R] (d : ℕ) (f : R[X][X])

/-- All coefficients outside the strict rectangular grid vanish. -/
def InBivariateGrid : Prop :=
  ∀ i j, d ≤ i ∨ d ≤ j → (f.coeff i).coeff j = 0

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
theorem bivariateGridPolynomial_reconstruct (hf : InBivariateGrid d f) :
    bivariateGridPolynomial R d (fun i => (f.coeff i.1.val).coeff i.2.val) = f := by
  ext i j
  by_cases hi : i < d
  · by_cases hj : j < d
    exact bivariateGridPolynomial_coeff _ ⟨i, hi⟩ ⟨j, hj⟩
    simp [bivariateGridPolynomial_coeff_zero d _ i j (Or.inr (by omega)), hf i j (Or.inr (by omega))]
  simp [bivariateGridPolynomial_coeff_zero d _ i j (Or.inl (by omega)), hf i j (Or.inl (by omega))]

/-- Every pair supported on the grid comes from a coefficient vector. -/
private theorem exists_closedFormPair_of_grid (u : R[X][X] × R[X][X]) (hp : InBivariateGrid d u.1)
    (hq : InBivariateGrid d u.2) :
    ∃ v, closedFormPair R d v = u := by
  refine ⟨Sum.elim (fun i => (u.1.coeff i.1.val).coeff i.2.val)
    (fun i => (u.2.coeff i.1.val).coeff i.2.val), ?_⟩
  solve_by_elim [Prod.ext, bivariateGridPolynomial_reconstruct]

end

variable {F : Type*} [Field F] (d : ℕ) (f : F[X][X])

/-- Two polynomial solutions, one not a scalar multiple of the other, give
a rank drop of at least two. -/
theorem closedForm_rank_drop_of_two_forms (u w : F[X][X] × F[X][X])
    (hu₁ : InBivariateGrid d u.1) (hu₂ : InBivariateGrid d u.2)
    (hw₁ : InBivariateGrid d w.1) (hw₂ : InBivariateGrid d w.2)
    (hu : closedFormOperator f u = 0) (hw : closedFormOperator f w = 0)
    (hu0 : u ≠ 0) (hind : ∀ a : F, a • u ≠ w) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  obtain ⟨v, hv⟩ := exists_closedFormPair_of_grid d u hu₁ hu₂
  obtain ⟨z, hz⟩ := exists_closedFormPair_of_grid d w hw₁ hw₂
  let V := (closedFormCoefficientMatrix d f).mulVecLin.ker
  have hvk := by
    apply (closedFormCoefficientMatrix_kernel d f v).mpr
    rw [hv, hu]
  have hzk := by
    apply (closedFormCoefficientMatrix_kernel d f z).mpr
    rw [hz, hw]
  let v' : V := ⟨v, hvk⟩
  have hv0 : v' ≠ 0 := by
    intro hh
    have hh'  := congrArg Subtype.val hh
    aesop
  have hi : LinearIndependent F ![v', ⟨z, hzk⟩] := by
    rw [LinearIndependent.pair_iff' hv0]
    intro a ha
    apply hind a
    have hh : a • v = z := congrArg Subtype.val ha
    rw [← hv, ← hz, ← (closedFormPair F d).map_smul, hh]
  have hdim := by simpa using hi.fintype_card_le_finrank
  have he := (closedFormCoefficientMatrix d f).mulVecLin.finrank_range_add_finrank_ker
  have hd : Module.finrank F (ClosedFormColumns d → F) = 2 * d ^ 2 := by
    simp [ClosedFormColumns, BivariateGrid, pow_two, two_mul]
  change (closedFormCoefficientMatrix d f).rank + Module.finrank F V = _ at he
  omega

end
end CCDN
