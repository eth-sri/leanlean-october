/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Plane.ScaledModelCoordinates
public import CCDN.Plane.ScaledPlaneCount
import CCDN.Algebra.HomogeneousSlice
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary
import CCDN.Plane.ScaledModelPosition

/-! The unit-scaled model gives a coefficient-uniform 2/d fallback and a
large-coefficient O(d^4) count, without requiring a scaling prime. -/

public section
namespace CCDN
open MvPolynomial Real

/-- The homogenization (with scaling factor `1`) of a primitive integer polynomial is
primitive. -/
lemma PrimitiveIntegerPolynomial.scaledHomogenize_one {n : ℕ}
    {f : CCDN.IntegerPolynomial n} (hf : PrimitiveIntegerPolynomial f) (d : ℕ) :
    PrimitiveIntegerPolynomial (CCDN.scaledHomogenize d 1 f) := by
  intro c hc
  apply hf c
  intro m
  have h := hc (homogenizedExponent d m)
  simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using h

private lemma unscaled_positioned_points_card_le {M t : ℕ}
    (f : CCDN.IntegerPolynomial 2) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (CCDN.rationalPolynomial f))
    (a : CCDN.IntPoint 2) (z : Fin t → CCDN.IntPoint 2) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) f = 0) (g : CCDN.IntegerPolynomial 3)
    (hg : IsPointAuxiliary (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree 1 f))
      g M (fun i j => eval (z i) (scaledModelCoordinates 1 a j))) :
    t ≤ f.totalDegree * M := by
  obtain ⟨g', hg', he, hnd'⟩ := scaledModelCoordinates_auxiliary_transport 1 a f g
    hg.isHomogeneous hg.not_dvd
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  have hchart : affineChart 2 (scaledHomogenize f.totalDegree 1 f) = f := by
    change homogeneousSlice 2 1 (scaledHomogenize f.totalDegree 1 f) = f
    simp only [homogeneousSlice_scaledHomogenize 1 f le_rfl, one_pow, map_one, one_mul]
  have hh := plane_chart_points_card_le_auxiliary_degree (scaledHomogenize f.totalDegree 1 f) g'
    (scaledHomogenize_homogeneous _ _ le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0)
    hg' (hprim.scaledHomogenize_one _) (by rw [hchart]) (by rwa [hchart]) hnd' z hinj
    (by simpa only [hchart] using hz) (fun i => (he (z i)).trans (hg.eval_eq_zero i))
  exact hh

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ} (f : CCDN.IntegerPolynomial 2) (hprim : PrimitiveIntegerPolynomial f) (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) (hd : 0 < f.totalDegree) (z : Fin t → CCDN.IntPoint 2) (hinj : Function.Injective z) {B C : ℝ} (hzB : IsBoxZeroFamily f B z) (hC : 0 ≤ C)

include hprim hir hd hinj hzB hC in
/-- Coefficient positioning removes the coefficient height from the 2/d
fallback bound. This holds for any primitive absolutely irreducible equation. -/
theorem unscaled_plane_finite_count
    
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    ↑t ≤ max
      (↑f.totalDegree * scaledPlaneAuxiliaryDegreeBound f.totalDegree C
        ((↑f.totalDegree + 1) * B) 1)
      ((34 + 8 * Real.exp (heightDeterminantError C + 20)) * ↑f.totalDegree ^ 4) := by
  obtain ⟨hB, hz, hbox⟩ := hzB
  let d := f.totalDegree
  let R := (↑d + 1) * B
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by linarith) hB
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  obtain ⟨a, H, ha, hH, _, hc, hlo, hhi⟩ := exists_scaled_model_position f hf0 hd  le_rfl
  let model := homogeneousTranslation ℤ a (scaledHomogenize d 1 f)
  have hmhom : model.IsHomogeneous d :=
    homogeneousTranslation_homogeneous a (scaledHomogenize_homogeneous _ _ le_rfl)
  have hm0 := by
    have he :=
      (homogeneousTranslation ℤ a).injective.ne (scaledHomogenize_ne_zero d one_ne_zero hf0)
    simpa only [map_zero] using he
  let τ := scaledModelCoordinates 1 a
  have hmodel : ∀ i, eval (fun j => eval (z i) (τ j)) model = 0 := by
    intro i
    change eval (fun j => eval (z i) (scaledModelCoordinates 1 a j))
      (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree 1 f)) = 0
    rw [scaledModelCoordinates_model_eval, hz i, mul_zero]
  have himagebox : ∀ i j, |(eval (z i) (τ j) : ℝ)| ≤ R := by
    grind [scaledModelCoordinates_box]
  have hirq := rational_irreducible_of_charZero_map f hir
  by_cases hsmall : Real.log H ≤ 4 * d * Real.log R
  · obtain ⟨M, hM, g, hg⟩ := polynomial_map_auxiliary_small_height_degree
      MonomialOrder.lex model hmhom hm0 hd ⟨rfl, hir, hH, hc⟩ τ z hz ⟨hR, hmodel, himagebox⟩ hC
      (hlo.trans hsmall) hcount
    have ht := unscaled_positioned_points_card_le f hprim hirq a z hinj hz g hg
    have htR : ↑t ≤ d * (M : ℝ) := by exact_mod_cast ht
    have hL : 0 < |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (MonomialOrder.lex.leadingCoeff_ne_zero_iff.mpr hm0))
    have hratio := scaled_positioned_height_ratio_le hd  le_rfl (by simpa using hH) hL hhi
    simp only [Real.log_one, zero_div, add_zero, Real.one_rpow, div_one] at hratio
    have ht := mul_le_mul_of_nonneg_left hratio (show 0 ≤
      2 * Real.exp (heightDeterminantError C + 23) * ↑d ^ 3 * R ^ (2 / (d : ℝ)) by positivity)
    have hterm : 2 * Real.exp (heightDeterminantError C + 23) * ↑d ^ 3 *
        (1 + Real.log H / ↑d ^ 2) * R ^ (2 / (d : ℝ)) /
          |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) ≤
        2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * ↑d ^ 3 *
          R ^ (2 / (d : ℝ)) := by
      convert ht using 1 <;> ring
    have hMb : (M : ℝ) ≤ scaledPlaneAuxiliaryDegreeBound d C R 1 := by
      unfold scaledPlaneAuxiliaryDegreeBound
      simp only [Real.log_one, zero_div, add_zero, mul_one, Real.one_rpow, div_one]
      linarith
    exact (htR.trans (mul_le_mul_of_nonneg_left hMb hdR.le)).trans (le_max_left _ _)
  · obtain ⟨M, hM, g, hg⟩ := polynomial_map_auxiliary_large_height_degree
      MonomialOrder.lex model hmhom hm0 hd ⟨rfl, hir, hH, hc⟩ τ z hz ⟨hR, hmodel, himagebox⟩ hC
      14 (by norm_num) (le_of_lt (lt_of_not_ge hsmall)) hhi hcount
    have ht := unscaled_positioned_points_card_le f hprim hirq a z hinj hz g hg
    have htR : ↑t ≤ d * (M : ℝ) := by exact_mod_cast ht
    apply (htR.trans (mul_le_mul_of_nonneg_left hM hdR.le)).trans
    calc
      _ = (34 + 8 * Real.exp (heightDeterminantError C + 20)) * ↑d ^ 4 := by
        ring
      _ ≤ _ := le_max_right _ _

include hprim hir hd hinj hzB hC in
/-- A sufficiently large coefficient forces the large-height branch
and gives O(d^4). -/
theorem unscaled_plane_finite_count_large_coefficient
    
    (m : Fin 2 →₀ ℕ) (hm : f.coeff m ≠ 0)
    (hheight : 4 * ↑f.totalDegree * Real.log ((↑f.totalDegree + 1) * B) ≤
      Real.log |(f.coeff m : ℝ)|)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    ↑t ≤ (34 + 8 * Real.exp (heightDeterminantError C + 20)) * ↑f.totalDegree ^ 4 := by
  obtain ⟨hB, hz, hbox⟩ := hzB
  let d := f.totalDegree
  let R := (↑d + 1) * B
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by linarith) hB
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  obtain ⟨a, H, ha, hH, _, hc, _, hhi⟩ := exists_scaled_model_position f hf0 hd (h := 1) le_rfl
  let model := homogeneousTranslation ℤ a (scaledHomogenize d 1 f)
  have hmhom : model.IsHomogeneous d :=
    homogeneousTranslation_homogeneous a (scaledHomogenize_homogeneous _ _ le_rfl)
  have hm0 := by
    have he :=
      (homogeneousTranslation ℤ a).injective.ne (scaledHomogenize_ne_zero d one_ne_zero hf0)
    simpa only [map_zero] using he
  let τ := scaledModelCoordinates 1 a
  have hmodel : ∀ i, eval (fun j => eval (z i) (τ j)) model = 0 := by
    intro i
    change eval (fun j => eval (z i) (scaledModelCoordinates 1 a j))
      (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree 1 f)) = 0
    rw [scaledModelCoordinates_model_eval, hz i, mul_zero]
  have himagebox : ∀ i j, |(eval (z i) (τ j) : ℝ)| ≤ R := by
    grind [scaledModelCoordinates_box]
  have hirq := rational_irreducible_of_charZero_map f hir
  have hlarge := hheight.trans
    (Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hm)) (hc m))
  obtain ⟨M, hM, g, hg⟩ := polynomial_map_auxiliary_large_height_degree
    MonomialOrder.lex model hmhom hm0 hd ⟨rfl, hir, hH, hc⟩ τ z hz ⟨hR, hmodel, himagebox⟩ hC
    14 (by norm_num) hlarge hhi hcount
  have ht := unscaled_positioned_points_card_le f hprim hirq a z hinj hz g hg
  have htR : ↑t ≤ d * (M : ℝ) := by exact_mod_cast ht
  have ht' := htR.trans (mul_le_mul_of_nonneg_left hM hdR.le)
  rw [show heightDeterminantError C + 6 + 14 = heightDeterminantError C + 20 by ring] at ht'
  convert ht' using 1
  ring

end CCDN
