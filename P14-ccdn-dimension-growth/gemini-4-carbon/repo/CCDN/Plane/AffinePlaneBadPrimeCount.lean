/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
public import CCDN.Statements
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.Plane.Bezout

/-! Plane-curve integral-point bounds from the `n = 0` specialization of
`affine_hypersurface_auxiliary`: both the logarithm-free bad-prime form and
the coefficient-uniform `PlaneCurveBound`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem affine_plane_expression_le_bad_prime {d : ℕ} (hd : 0 < d)
    {B L b : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineAuxiliaryDegreeExpression 0 d B L b ≤
      (d : ℝ) ^ 3 * (b + 2) * B ^ (1 / (d : ℝ)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hdR
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  have hlogL := Real.log_nonneg hL
  have hpow : 1 ≤ B ^ (1 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have hden : 1 ≤ L ^ (1 / ((d : ℝ) * d)) := Real.one_le_rpow hL (by positivity)
  have hmin : 0 ≤ min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) :=
    le_min (by positivity) (by positivity)
  have hfrac :
      (d : ℝ) * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
        B ^ (1 / (d : ℝ)) / L ^ (1 / ((d : ℝ) * d)) ≤
      (d : ℝ) ^ 3 * b * B ^ (1 / (d : ℝ)) := by
    calc
      _ ≤ (d : ℝ) *
          min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
          B ^ (1 / (d : ℝ)) := div_le_self (by positivity) hden
      _ ≤ (d : ℝ) * ((d : ℝ) ^ 2 * b) * B ^ (1 / (d : ℝ)) := by
        gcongr
        exact min_le_right _ _
      _ = _ := by ring
  have hlog : Real.log B ≤ (d : ℝ) * B ^ (1 / (d : ℝ)) :=
    log_le_dimension_root hd hB0
  have hdcube : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hdR (by omega : 1 ≤ 3)
  have hlog' := hlog.trans (mul_le_mul_of_nonneg_right hdcube (by positivity))
  have hcube := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (d : ℝ) ^ 3 by positivity)
  unfold affineAuxiliaryDegreeExpression
  norm_num only [Nat.cast_zero, zero_add, div_one, Real.rpow_one, Real.rpow_zero,
    one_mul, sub_self, mul_one, show (2 - 1 : ℝ) = 1 by norm_num,
    show (4 - 1 : ℝ) = 3 by norm_num, Real.rpow_natCast, Real.rpow_ofNat]
  nlinarith

private theorem affine_plane_expression_le_curveBound {d : ℕ} (hd : 0 < d)
    {B L b : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineAuxiliaryDegreeExpression 0 d B L b ≤
      4 * (d : ℝ) ^ 2 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hdR
  have hlogB := Real.log_nonneg hB
  have hlogL := Real.log_nonneg hL
  have hpow : 1 ≤ B ^ (1 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  set u := L ^ (1 / ((d : ℝ) * d))
  have hu1 : 1 ≤ u := Real.one_le_rpow hL (by positivity)
  have hlogL_le : Real.log L ≤ (d : ℝ) ^ 2 * u := by
    have h1 : Real.log u = Real.log L / (d : ℝ) ^ 2 := by
      rw [Real.log_rpow (zero_lt_one.trans_le hL)]; ring
    have h2 : Real.log u ≤ u := Real.log_le_self (by positivity)
    rw [h1, div_le_iff₀ (by positivity)] at h2
    linarith
  have hmin : 0 ≤ min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) :=
    le_min (by positivity) (by positivity)
  have hfrac : (d : ℝ) * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
      B ^ (1 / (d : ℝ)) / u ≤ 2 * (d : ℝ) ^ 2 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
    rw [div_le_iff₀ (by positivity)]
    have hm : min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) ≤
        Real.log L + d * Real.log B + (d : ℝ) ^ 2 := min_le_left _ _
    have hnum : Real.log L + d * Real.log B + (d : ℝ) ^ 2 ≤ 2 * d * (Real.log B + d) * u := by
      have : (d : ℝ) * Real.log B + (d : ℝ) ^ 2 ≤ ((d : ℝ) * Real.log B + (d : ℝ) ^ 2) * u :=
        le_mul_of_one_le_right (by positivity) hu1
      have : (d : ℝ) ^ 2 + ((d : ℝ) * Real.log B + (d : ℝ) ^ 2) ≤ 2 * d * (Real.log B + d) := by
        nlinarith [mul_le_mul_of_nonneg_right hdR hlogB]
      nlinarith
    have hprod := mul_le_mul_of_nonneg_left (hm.trans hnum)
      (show 0 ≤ (d : ℝ) * B ^ (1 / (d : ℝ)) by positivity)
    nlinarith
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hrem : Real.log B + (d : ℝ) ^ 3 ≤ 2 * (d : ℝ) ^ 2 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
    have h1 : Real.log B + d ≤ (d : ℝ) ^ 2 * B ^ (1 / (d : ℝ)) * (Real.log B + d) :=
      le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hd2 hpow)
    have h2 : (d : ℝ) ^ 3 = (d : ℝ) ^ 2 * 1 * d := by ring
    have h3 : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 2 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
      rw [h2]; gcongr; linarith
    linarith
  unfold affineAuxiliaryDegreeExpression
  norm_num only [Nat.cast_zero, zero_add, div_one, Real.rpow_one, Real.rpow_zero,
    one_mul, sub_self, mul_one, show (2 - 1 : ℝ) = 1 by norm_num,
    show (4 - 1 : ℝ) = 3 by norm_num, Real.rpow_natCast, Real.rpow_ofNat]
  linarith

private theorem integer_plane_count_of_auxiliary
    (f g : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom ℚ) f)) {B R : ℝ}
    (hg : IsBoxAuxiliary f g B) (hgdeg : (g.totalDegree : ℝ) ≤ R) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ f.totalDegree * R := by
  obtain ⟨_, hfg, hgz⟩ := hg
  have hfgQ : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g :=
    fun h => hfg (hprim.rational_map_dvd_iff.mp h)
  apply integer_zero_count_le_of_family_bound
  intro t z hinj hzf hbox
  have hzQ : Function.Injective (fun i => rationalPoint (z i)) := fun i j h =>
    hinj (funext fun k => Int.cast_injective (congrFun h k))
  have hmapzero (p : MvPolynomial (Fin 2) ℤ) (i : Fin t) (hp : eval (z i) p = 0) :
      eval (rationalPoint (z i)) (map (Int.castRingHom ℚ) p) = 0 := by
    have hh := congrArg (Int.castRingHom ℚ) hp
    rwa [map_eval, map_zero] at hh
  have hbezout := plane_common_zeros_card_le (map (Int.castRingHom ℚ) f)
    (map (Int.castRingHom ℚ) g) hir hfgQ (fun i => rationalPoint (z i)) hzQ
    (fun i => hmapzero f i (hzf i)) (fun i => hmapzero g i (hgz (z i) (hbox i) (hzf i)))
  rw [Fintype.card_fin, rational_map_totalDegree, rational_map_totalDegree] at hbezout
  exact (show (t : ℝ) ≤ (f.totalDegree : ℝ) * g.totalDegree by exact_mod_cast hbezout).trans
    (mul_le_mul_of_nonneg_left hgdeg (Nat.cast_nonneg _))

/-- The plane auxiliary and Bezout prove the bad-prime bound for integer zeros. -/
theorem affine_plane_count_bad_prime
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      affineHypersurfaceAuxiliaryConstant 0 * (f.totalDegree : ℝ) ^ 4 *
        (hypersurfaceBadPrimeFactor f + 2) * B ^ (1 / (f.totalDegree : ℝ)) := by
  obtain ⟨g, hg, hgdeg⟩ :=
    affine_hypersurface_auxiliary f hprim (hprim.irreducible_of_rational_map hir) hd hB
  have hf0 : f ≠ 0 := ne_zero_of_irreducible_map hir
  have hdegree := hgdeg.trans (mul_le_mul_of_nonneg_left
    (affine_plane_expression_le_bad_prime hd hB (leading_height_one_le f hf0)
      (hypersurfaceBadPrimeFactor_nonneg f)) (affineHypersurfaceAuxiliaryConstant_pos 0).le)
  exact (integer_plane_count_of_auxiliary f g hprim hir hg hdegree).trans_eq (by ring)

/-- `d⁴ ≤ curveBound d B` for `d > 0` and `B ≥ 1`. -/
lemma degree_four_le_curveBound {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    (d : ℝ) ^ 4 ≤ curveBound d B := by
  have hB1 : 1 ≤ B ^ (1 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have hlog := Real.log_nonneg hB
  unfold curveBound
  calc (d : ℝ) ^ 4 = (d : ℝ) ^ 3 * 1 * d := by ring
    _ ≤ (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by gcongr; linarith

/-- Explicit uniform affine plane curve bound for rational irreducible equations. -/
theorem rational_plane_curve_count (f : MvPolynomial (Fin 2) ℚ) (hir : Irreducible f)
    (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤
      (4 * affineHypersurfaceAuxiliaryConstant 0) * curveBound f.totalDegree B := by
  obtain ⟨g₀, a, hprim, ha, he⟩ := exists_primitive_integer_model f hir.ne_zero
  have hdeg := rational_scalar_model_degree ha hir.ne_zero he
  have hg0_ir : Irreducible (map (Int.castRingHom ℚ) g₀) := by
    rw [he]
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr ha).map C)).mpr hir
  have hgd : 0 < g₀.totalDegree := hdeg.symm ▸ hd
  have hzero : zeroLocus (map (Int.castRingHom ℚ) g₀) = zeroLocus f :=
    Set.ext fun x => rational_scalar_model_zero_iff ha he x
  obtain ⟨g, hg, hgdeg⟩ := affine_hypersurface_auxiliary g₀ hprim
    (hprim.irreducible_of_rational_map hg0_ir) hgd hB
  have hdegree := hgdeg.trans (mul_le_mul_of_nonneg_left
    (affine_plane_expression_le_curveBound hgd hB
      (leading_height_one_le g₀ (ne_zero_of_irreducible_map hg0_ir))
      (hypersurfaceBadPrimeFactor_nonneg g₀))
    (affineHypersurfaceAuxiliaryConstant_pos 0).le)
  rw [← hzero, ← hdeg]
  exact (integer_plane_count_of_auxiliary g₀ g hprim hg0_ir hg hdegree).trans_eq
    (by unfold curveBound; ring)

/-- The full coefficient-uniform rational-plane integral-point bound. -/
theorem planeCurveBound : PlaneCurveBound :=
  ⟨4 * affineHypersurfaceAuxiliaryConstant 0,
    mul_pos (by norm_num) (affineHypersurfaceAuxiliaryConstant_pos 0),
    fun f hir hd _ hB => rational_plane_curve_count f hir hd hB⟩

end
end CCDN
