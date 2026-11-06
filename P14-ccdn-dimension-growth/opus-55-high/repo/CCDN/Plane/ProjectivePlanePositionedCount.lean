/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousChart
import CCDN.Height.ProjectiveBox
import CCDN.Plane.ScaledPlaneCount
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Algebra.ProjectiveTranslation
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.ProjectiveAuxiliaryCount
import CCDN.Plane.ScaledModelPosition

/-! Coefficient-uniform projective plane counts after a bounded integral
coordinate change. The finite-field and positioning inputs are proved. -/

namespace CCDN
section
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] (f : MvPolynomial (Fin 3) ℤ)

/-- Coefficient-uniform projective plane count: for a primitive ternary integer form `f` of degree
`d ≥ 2`, absolutely irreducible over an algebraically closed field of characteristic zero, the
number of distinct projective points with primitive integer coordinates in the box of size `B` on
`f = 0` is at most the maximum of the two degree bounds of the scaled plane count with residue
constant `projectivePlaneDeterminantConstant`. The proof first moves `f` by a bounded integral
coordinate change. -/
theorem projective_plane_finite_count_positioned
    [IsAlgClosed K] {d t : ℕ}
    (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint 3) (hz0 : ∀ i, z i ≠ 0)
    (hinj : Function.Injective (fun i => Projectivization.mk ℚ (rationalPoint (z i))
      (rationalPoint_ne_zero (hz0 i))))
    {B : ℝ} (hzB : IsPrimitiveBoxZeroFamily f B z) :
    (t : ℝ) ≤ max
      ((d : ℝ) * scaledPlaneAuxiliaryDegreeBound d projectivePlaneDeterminantConstant (((d : ℝ) +
          1) * B) 1)
      ((34 + 8 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 20)) *
          (d : ℝ) ^ 4) := by
  obtain ⟨⟨hB, hz, hbox⟩, hzprim⟩ := hzB
  have hdpos : 0 < d := by omega
  obtain ⟨a, H, ha, hH, -, hc, hlo, hhi⟩ := exists_translated_coefficient_position hdpos f hf (by aesop)
  let model := homogeneousTranslation ℤ a f
  have hmhom := homogeneousTranslation_homogeneous a hf
  have hm0 : model ≠ 0 := by aesop
  have hmir : Irreducible (map (Int.castRingHom K) model) := by
    rw [homogeneousTranslation_map]
    exact (MulEquiv.irreducible_iff
      (f := homogeneousTranslation K ((Int.castRingHom K) ∘ a))).mpr hir
  obtain ⟨hmdeg, hmchart⟩ : (affineChart 2 model).totalDegree = d ∧
      Irreducible (map (Int.castRingHom K) (affineChart 2 model)) := by
    have hirQ := rational_irreducible_of_charZero_map model hmir
    have hQ := affineChart_degree_of_not_variable_dvd _ (hmhom.map _)
      (variable_not_dvd_irreducible_homogeneous _ (hmhom.map _) hirQ hd 0)
    rw [affineChart_map, rational_map_totalDegree] at hQ
    refine ⟨hQ, ?_⟩
    rw [← affineChart_map]
    exact affineChart_irreducible_of_not_variable_dvd _ (hmhom.map _) hmir
      (variable_not_dvd_irreducible_homogeneous _ (hmhom.map _) hmir hd 0)
  let w := fun i => homogeneousPointTranslation (-a) (z i)
  have hw0 := fun i => homogeneousPointTranslation_ne_zero (-a) (hz0 i)
  have hwi : Function.Injective (fun i => Projectivization.mk ℚ
      (rationalPoint (homogeneousPointTranslation (-a) (z i)))
      (rationalPoint_ne_zero (homogeneousPointTranslation_ne_zero (-a) (hz0 i)))) := by
    intro i j he
    apply hinj
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp he
    apply (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mpr
    refine ⟨c, ?_⟩
    change (c : ℚ) • ((Int.castRingHom ℚ) ∘ homogeneousPointTranslation (-a) (z j)) =
      (Int.castRingHom ℚ) ∘ homogeneousPointTranslation (-a) (z i) at hc
    rw [homogeneousPointTranslation_map, homogeneousPointTranslation_map,
      ← homogeneousPointTranslation_smul] at hc
    exact homogeneousPointTranslation_injective _ hc
  have hwp : ∀ i, Finset.univ.gcd (w i) = 1 := by
    intro i
    exact (homogeneousPointTranslation_gcd (-a) (z i)).trans (hzprim i)
  have hwz : ∀ i, eval (w i) model = 0 := by
    intro i
    rw [homogeneousTranslation_eval]
    change eval (homogeneousPointTranslation a (homogeneousPointTranslation (-a) (z i))) f = 0
    have he := homogeneousPointTranslation_inverse (-a) (z i)
    simp_all
  let R := (d + 1) * B
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le
    (by grind) hB
  have hwbox :=
    fun i j => homogeneousPointTranslation_box hB a ha (z i) (hbox i) j
  have hmp := hprim.translate_homogeneous a
  by_cases hsmall : Real.log H ≤ 4 * d * Real.log R
  · have ht := projective_points_small_height_bound MonomialOrder.lex model hmhom hm0 hd hmp
      ⟨hmdeg, hmchart, hH, hc⟩ w hw0 hwi ⟨⟨hR, hwz, hwbox⟩, hwp⟩ (hlo.trans hsmall)
    have hL : 0 < |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (MonomialOrder.lex.leadingCoeff_ne_zero_iff.mpr hm0))
    have hratio := scaled_positioned_height_ratio_le hdpos le_rfl
      (by simp_all) hL hhi
    simp at hratio
    have hterm := mul_le_mul_of_nonneg_left hratio (show 0 ≤
      2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) * d ^ 3 *
          R ^ (2 / (d : ℝ))
      by positivity)
    have hbound : (d : ℝ) + Real.log R +
        2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
            (d : ℝ) ^ 3 *
          (1 + Real.log H / (d : ℝ) ^ 2) * R ^ (2 / (d : ℝ)) /
            |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2 ≤
        scaledPlaneAuxiliaryDegreeBound d projectivePlaneDeterminantConstant R 1 := by
      unfold scaledPlaneAuxiliaryDegreeBound
      simp
      ring_nf at hterm ⊢
      linarith
    exact (ht.trans (mul_le_mul_of_nonneg_left hbound (by positivity))).trans (le_max_left _ _)
  · have ht := projective_points_large_height_bound MonomialOrder.lex model hmhom hm0 hd hmp
      ⟨hmdeg, hmchart, hH, hc⟩ w hw0 hwi ⟨⟨hR, hwz, hwbox⟩, hwp⟩ 14 (by norm_num)
      (le_of_lt (lt_of_not_ge hsmall)) hhi
    grind

