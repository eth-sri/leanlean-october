/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.LowerBound.GridEisenstein
import CCDN.Noether.BivariateTotalDegree
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-! Exact total degree and coefficient extension for the explicit grid equation. -/

namespace CCDN
open Polynomial

section
variable {R : Type*} [CommRing R]

lemma bivariateTotalDegree_add_le (f g : R[X][X]) :
    bivariateTotalDegree (f + g) ≤ max (bivariateTotalDegree f) (bivariateTotalDegree g) := by
  unfold bivariateTotalDegree
  rw [map_add]
  exact MvPolynomial.totalDegree_add _ _

lemma bivariateTotalDegree_C_le (f : R[X]) :
    bivariateTotalDegree (C f) ≤ f.natDegree := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  by_cases hi : i = 0
  · subst i
    simpa using le_natDegree_of_ne_zero (by simp_all)
  · aesop

lemma bivariateTotalDegree_map_C_le (f : R[X]) :
    bivariateTotalDegree (f.map C) ≤ f.natDegree := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  by_cases hj : j = 0
  · subst j
    simpa using le_natDegree_of_ne_zero (by simp_all)
  · aesop

end

section
variable {K : Type*} [Field K] (V : K[X]) (k : ℕ)

lemma gridEisensteinCorrection_monic_degree
    (hm : V.Monic) (hk : 2 ≤ k) :
    IsMonicOfDegree (gridEisensteinCorrection V k) (V.natDegree + k) := by
  apply IsMonicOfDegree.mul (show IsMonicOfDegree V V.natDegree from ⟨rfl, hm⟩)
  apply (isMonicOfDegree_X_pow K k).add_right
  have h : (C (V.coeff 1 / V.coeff 0 + 1) * X).natDegree ≤ 1 := by
    simpa using (natDegree_mul_le (p := (C (V.coeff 1 / V.coeff 0 + 1) : K[X])) (q := X))
  omega

end

variable {K L : Type*} [Field K] [Field L] (φ : K →+* L) (V : K[X]) (k : ℕ)

lemma gridEisensteinCorrection_map
    :
    (gridEisensteinCorrection V k).map φ = gridEisensteinCorrection (V.map φ) k := by
  simp [gridEisensteinCorrection]

lemma gridEisensteinPolynomial_map
    :
    bivariateMap φ (gridEisensteinPolynomial V k) = gridEisensteinPolynomial (V.map φ) k := by
  have he : (Polynomial.mapRingHom φ).comp C = C.comp φ := by aesop
  change (gridEisensteinPolynomial V k).map (Polynomial.mapRingHom φ) = _
  simp [gridEisensteinPolynomial, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, coe_mapRingHom, map_map, he, gridEisensteinCorrection_map,
    coeff_map, natDegree_map_eq_of_injective φ.injective, map_inv₀]

