/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.LowerBound.GridEisensteinDegree
import CCDN.Noether.ShearNormalization
import CCDN.Plane.GridHeight

/-! Absolutely irreducible plane equations through arbitrary finite square
Cartesian grids. Translation moves the Eisenstein place away from the grid. -/

public section
namespace CCDN
open Polynomial

variable {K : Type*} [Field K]


private lemma grid_root_polynomial_eval_zero 
    (s : Finset K) {a : K} (ha : a ∈ s) :
    (∏ b ∈ s, (X - C b : K[X])).eval a = 0 := by
  rw [eval_prod]
  exact Finset.prod_eq_zero ha (by simp)

/-- An arbitrary finite square grid of side s lies on an absolutely irreducible
curve of every degree d≥s+2 satisfying 2s≤d+1, given by an explicit equation. -/
theorem exists_absolutely_irreducible_plane_grid
    {K L : Type*} [Field K] [Infinite K] [Field L] (φ : K →+* L)
    (s : Finset K) (hs : 0 < s.card) (d : ℕ)
    (hd : s.card + 2 ≤ d) (hsize : 2 * s.card ≤ d + 1) :
    ∃ f : MvPolynomial (Fin 2) K,
      f.totalDegree = d ∧ Irreducible (MvPolynomial.map φ f) ∧
        ∀ z : Fin 2 → K, (∀ i, z i ∈ s) → MvPolynomial.eval z f = 0 := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset s
  let t := s.image (fun x => x - a)
  have ht : t.card = s.card := Finset.card_image_of_injective _ (fun _ _ h => sub_left_inj.mp h)
  have ht0 : 0 ∉ t := by
    grind
  let V := ∏ x ∈ t, (X - C x)
  have hm := monic_prod_X_sub_C id t
  have hvdeg : V.natDegree = s.card := (natDegree_finsetProd_X_sub_C_eq_card t id).trans ht
  have hv0 := (show (∏ a ∈ t, (X - C a)).coeff (0 : ℕ) ≠ (0 : K) from (by
                rw [coeff_zero_eq_eval_zero]
                simp only [eval_prod, eval_sub, eval_X, eval_C, zero_sub]
                apply Finset.prod_ne_zero_iff.mpr
                intro a ha
                exact neg_ne_zero.mpr (by intro h; subst a; exact ht0 ha)))
  let k := d - s.card
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hvs : V.natDegree ≤ k + 1 := by dsimp [k]; omega
  have hvpos : 0 < V.natDegree := by omega
  let g := (bivariatePolynomialEquiv K).symm (gridEisensteinPolynomial V k)
  have hgdeg : g.totalDegree = d := by
    change bivariateTotalDegree (gridEisensteinPolynomial V k) = _
    rw [gridEisensteinPolynomial_totalDegree V k hm hvpos hv0 hk hvs, hvdeg]
    dsimp [k]
    omega
  have hgir : Irreducible (MvPolynomial.map φ g) := by
    apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)).mp
    rw [← bivariatePolynomialEquiv_map]
    rw [AlgEquiv.apply_symm_apply]
    exact gridEisensteinPolynomial_map_irreducible φ V k hm hvpos hv0 hk
  refine ⟨affineTranslation K (fun _ => -a) g, ?_, ?_, ?_⟩
  · rwa [affineTranslation_totalDegree]
  · simp_all [affineTranslation_map, affineTranslation_irreducible_iff]
  · intro z hz
    rw [affineTranslation_eval]
    have hzV (i) : V.eval (z i - a) = 0 :=
      grid_root_polynomial_eval_zero t (Finset.mem_image.mpr ⟨z i, hz i, rfl⟩)
    have hh := gridEisensteinPolynomial_eval_zero V k (z 0 - a) (z 1 - a) (hzV 0) (hzV 1)
    have he := bivariatePolynomialEquiv_eval g (z 0 - a) (z 1 - a)
    rw [AlgEquiv.apply_symm_apply, hh] at he
    have hzvec : z + (fun _ => -a) = ![z 0 - a, z 1 - a] := by
      funext i
      fin_cases i <;> simp [sub_eq_add_neg]
    rw [hzvec]
    exact he.symm

end CCDN
