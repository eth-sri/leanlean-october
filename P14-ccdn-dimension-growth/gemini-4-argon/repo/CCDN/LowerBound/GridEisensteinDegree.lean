/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.LowerBound.GridEisenstein
public import CCDN.Noether.BivariateTotalDegree
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-! Exact total degree and coefficient extension for the explicit grid equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- If s≤k+1, the explicit equation has exact total degree s+k. -/
theorem gridEisensteinPolynomial_totalDegree {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree)
    (h0 : V.coeff 0 ≠ 0) (hk : 2 ≤ k) (hs : V.natDegree ≤ k + 1) :
    bivariateTotalDegree (gridEisensteinPolynomial V k) = V.natDegree + k := by
  have hadd (f g : K[X][X]) :
      bivariateTotalDegree (f + g) ≤ max (bivariateTotalDegree f) (bivariateTotalDegree g) := by
    unfold bivariateTotalDegree; rw [map_add]; exact MvPolynomial.totalDegree_add _ _
  have hC (f : K[X]) : bivariateTotalDegree (C f) ≤ f.natDegree := by
    rw [bivariateTotalDegree_le_iff]; intro i j hij
    by_cases hi : i = 0
    · subst i; simpa using le_natDegree_of_ne_zero (by simpa using hij : f.coeff j ≠ 0)
    · simp [coeff_C, hi] at hij
  have hmapC (f : K[X]) : bivariateTotalDegree (f.map C) ≤ f.natDegree := by
    rw [bivariateTotalDegree_le_iff]; intro i j hij
    by_cases hj : j = 0
    · subst j; simpa using le_natDegree_of_ne_zero (by simpa using hij : f.coeff i ≠ 0)
    · simp [coeff_map, coeff_C, hj] at hij
  have hcorr : IsMonicOfDegree (gridEisensteinCorrection V k) (V.natDegree + k) := by
    refine IsMonicOfDegree.mul ⟨rfl, hm⟩ ((isMonicOfDegree_X_pow K k).add_right ?_)
    have h : (C (V.coeff 1 / V.coeff 0 + 1) * X).natDegree ≤ 1 := by
      simpa using natDegree_mul_le (p := (C (V.coeff 1 / V.coeff 0 + 1) : K[X])) (q := X)
    omega
  refine le_antisymm ?_ ?_
  · unfold gridEisensteinPolynomial
    refine (hadd _ _).trans (max_le ((hadd _ _).trans
      (max_le ((hmapC V).trans (by omega)) ?_))
      ((hC _).trans hcorr.natDegree_eq.le))
    have hsub : (X ^ V.natDegree - V).natDegree < V.natDegree :=
      IsMonicOfDegree.natDegree_sub_lt (ne_of_gt hd) (isMonicOfDegree_X_pow K _) ⟨rfl, hm⟩
    rw [show (X ^ V.natDegree : K[X][X]) - V.map C = (X ^ V.natDegree - V).map C by simp]
    have h₁ := (hC (V * C (V.coeff 0)⁻¹)).trans (natDegree_mul_C_le _ _)
    have h₂ := hmapC (X ^ V.natDegree - V)
    exact (bivariateTotalDegree_mul_le _ _).trans (by omega)
  · have hc0 : (gridEisensteinPolynomial V k).coeff 0 =
        C (V.coeff 0) - V + gridEisensteinCorrection V k := by
      rw [gridEisensteinPolynomial_coeff]
      simp only [coeff_X_pow, ne_of_lt hd, ite_false, zero_sub, ite_true]
      rw [mul_neg, mul_assoc, ← C_mul, inv_mul_cancel₀ h0, C_1, mul_one]; rfl
    have h1 : ((gridEisensteinPolynomial V k).coeff 0).coeff (V.natDegree + k) = 1 := by
      rw [hc0, coeff_add, coeff_sub, coeff_C, ite_eq_right (by omega : V.natDegree + k ≠ 0),
        coeff_eq_zero_of_natDegree_lt (by omega), zero_sub, neg_zero, zero_add, ← hcorr.natDegree_eq]
      exact hcorr.monic.coeff_natDegree
    simpa using bivariateTotalDegree_coeff_le (gridEisensteinPolynomial V k) 0 (V.natDegree + k)
      (by rw [h1]; exact one_ne_zero)

/-- Absolute irreducibility is stable under every field extension here because
Eisenstein applies to the same explicit equation after coefficient extension. -/
theorem gridEisensteinPolynomial_map_irreducible {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (V : K[X]) (k : ℕ) (hm : V.Monic)
    (hd : 0 < V.natDegree) (h0 : V.coeff 0 ≠ 0) (hk : 2 ≤ k) :
    Irreducible (bivariateMap φ (gridEisensteinPolynomial V k)) := by
  have he : (Polynomial.mapRingHom φ).comp C = C.comp φ := by ext a; simp
  have hcorr : (gridEisensteinCorrection V k).map φ = gridEisensteinCorrection (V.map φ) k := by
    simp [gridEisensteinCorrection]
  have hmap : bivariateMap φ (gridEisensteinPolynomial V k) =
      gridEisensteinPolynomial (V.map φ) k := by
    change (gridEisensteinPolynomial V k).map (Polynomial.mapRingHom φ) = _
    simp only [gridEisensteinPolynomial, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, coe_mapRingHom, map_map, he, hcorr, coeff_map,
      natDegree_map_eq_of_injective φ.injective, map_inv₀]
  rw [hmap]
  exact gridEisensteinPolynomial_irreducible _ k (hm.map φ)
    (by rwa [natDegree_map_eq_of_injective φ.injective])
    (by simpa only [coeff_map, map_ne_zero_iff φ φ.injective] using h0) hk

end
end CCDN
