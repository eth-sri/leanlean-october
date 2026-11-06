/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.LowerBound.GridEisensteinDegree
import CCDN.Noether.ShearNormalization
import CCDN.Plane.GridHeight

/-! Absolutely irreducible plane equations through arbitrary finite square
Cartesian grids. Translation moves the Eisenstein place away from the grid. -/

namespace CCDN
section
open Polynomial

section
variable {K : Type*} [Field K] (s : Finset K)

end

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
  have ht0 : 0 ∉ t := by grind
  let V : K[X] := ∏ x ∈ t, (X - C x)
  have hm := monic_prod_X_sub_C id t
  have hvdeg : V.natDegree = s.card := (natDegree_finsetProd_X_sub_C_eq_card t id).trans ht
  have hv0 : (∏ a ∈ t, (X - C a : K[X])).coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [eval_prod, eval_sub, eval_X, eval_C, zero_sub]
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact neg_ne_zero.mpr (by grind)
  let k := d - s.card
  have hk : 2 ≤ k := by grind
  have hvs : V.natDegree ≤ k + 1 := by grind
  have hvpos : 0 < V.natDegree := by omega
  let g := (bivariatePolynomialEquiv K).symm (gridEisensteinPolynomial V k)
  have hgdeg : g.totalDegree = d := by
    change bivariateTotalDegree (gridEisensteinPolynomial V k) = _
    rw [(show bivariateTotalDegree (gridEisensteinPolynomial V k) = V.natDegree + k by
        apply le_antisymm (show bivariateTotalDegree (gridEisensteinPolynomial V k) ≤ V.natDegree + k by
            apply (bivariateTotalDegree_add_le _ _).trans
            apply max_le
            · apply (bivariateTotalDegree_add_le _ _).trans
              apply max_le
              · exact (bivariateTotalDegree_map_C_le V).trans (by omega)
              · have hsub :=
                  IsMonicOfDegree.natDegree_sub_lt hvpos.ne'
                    (isMonicOfDegree_X_pow K _) ⟨rfl, hm⟩
                have he : (X ^ V.natDegree : K[X][X]) - V.map C =
                    (X ^ V.natDegree - V).map C := by simp
                rw [he]
                apply (bivariateTotalDegree_mul_le _ _).trans
                have h₁ := bivariateTotalDegree_C_le (V * C (V.coeff 0)⁻¹)
                have h₂ := bivariateTotalDegree_map_C_le (X ^ V.natDegree - V)
                have h₃ : (V * C (V.coeff 0)⁻¹).natDegree ≤ V.natDegree := natDegree_mul_C_le _ _
                omega
            · exact (bivariateTotalDegree_C_le _).trans
                (gridEisensteinCorrection_monic_degree V k hm hk).natDegree_eq.le)
        have hh := bivariateTotalDegree_coeff_le (gridEisensteinPolynomial V k) 0
          (V.natDegree + k)
          (by rw [(show ((gridEisensteinPolynomial V k).coeff 0).coeff (V.natDegree + k) = 1 by
              rw [(show (gridEisensteinPolynomial V k).coeff 0 =
                    C (V.coeff 0) - V + gridEisensteinCorrection V k by
                  rw [gridEisensteinPolynomial_coeff]
                  simp only [coeff_X_pow, hvpos.ne, ite_false, zero_sub, ite_true]
                  rw [mul_neg, mul_assoc, ← C_mul, inv_mul_cancel₀ hv0, C_1, mul_one]
                  rfl), coeff_add, coeff_sub]
              rw [coeff_C, ite_eq_right (by grind), coeff_eq_zero_of_natDegree_lt (by omega), zero_sub, neg_zero, zero_add]
              have h := gridEisensteinCorrection_monic_degree V k hm hk
              rw [← h.natDegree_eq]
              exact h.monic.coeff_natDegree)]; exact one_ne_zero)
        simpa using hh), hvdeg]
    grind
  have hgir : Irreducible (MvPolynomial.map φ g) := by
    apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)).mp
    rw [← bivariatePolynomialEquiv_map, AlgEquiv.apply_symm_apply, gridEisensteinPolynomial_map]
    apply gridEisensteinPolynomial_irreducible _ k (hm.map φ)
    · simp_all
    · simp_all
    · exact hk
  refine ⟨affineTranslation K (fun _ => -a) g, ?_, ?_, ?_⟩
  · rwa [affineTranslation_totalDegree]
  · rwa [affineTranslation_map, affineTranslation_irreducible_iff]
  · intro z hz
    rw [affineTranslation_eval]
    have hzV (i) : V.eval (z i - a) = 0 :=
      by
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨z i, hz i, rfl⟩) (by simp)
    have hh : ((gridEisensteinPolynomial V k).map (evalRingHom (z 1 - a))).eval (z 0 - a) = 0 := by
      have he : (evalRingHom (z 1 - a)).comp C = RingHom.id K := by aesop
      simp [gridEisensteinPolynomial, gridEisensteinCorrection, map_map, he, (hzV 0), (hzV 1)]
    have he := bivariatePolynomialEquiv_eval g (z 0 - a) (z 1 - a)
    rw [AlgEquiv.apply_symm_apply, hh] at he
    have hzvec : z + (fun _ => -a) = ![z 0 - a, z 1 - a] := by
      funext i
      fin_cases i <;> simp [sub_eq_add_neg]
    grind

