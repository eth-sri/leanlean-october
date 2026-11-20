/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import CCDN.Height.Box
public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
public import CCDN.Statements
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.Plane.Bezout

/-! The affine hypersurface auxiliary theorem gives both plane-curve estimates
via Bézout: the uniform bound and the bound in terms of the bad-prime factor. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma degree_four_le_curveBound {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    (d : ℝ) ^ 4 ≤ curveBound d B := by
  have hQ := Real.one_le_rpow hB (show 0 ≤ 1 / (d : ℝ) by positivity)
  have := Real.log_nonneg hB
  unfold curveBound
  calc _ = (d : ℝ) ^ 3 * 1 * d := by ring
       _ ≤ _ := by gcongr; linarith

private theorem affine_plane_count_le_auxiliary_expression
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom ℚ) f)) (hd : 0 < f.totalDegree)
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      (f.totalDegree : ℝ) * (affineHypersurfaceAuxiliaryConstant 0 *
        affineAuxiliaryDegreeExpression 0 f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (hypersurfaceBadPrimeFactor f)) := by
  classical
  obtain ⟨g, ⟨_, hfg, hgz⟩, hgdeg⟩ :=
    affine_hypersurface_auxiliary f hprim (hprim.irreducible_of_rational_map hir) hd hB
  let S := integralPoints (zeroLocus (map (Int.castRingHom ℚ) f)) B
  let z : S → RatPoint 2 := fun i => rationalPoint i.val
  have hz : Function.Injective z := (rationalPoint_injective _).comp Subtype.val_injective
  have hm (x : S) := mem_integralPoints.mp x.property
  have hbezout := plane_common_zeros_card_le (map (Int.castRingHom ℚ) f)
    (map (Int.castRingHom ℚ) g) hir (fun h => hfg (hprim.rational_map_dvd_iff.mp h)) z hz
    (fun x => (hm x).2) (fun x => (eval_rationalPoint_map_eq_zero x.val g).mpr
      (hgz x.val (hm x).1 ((eval_rationalPoint_map_eq_zero x.val f).mp (hm x).2)))
  rw [Fintype.card_coe, totalDegree_map_of_injective Int.cast_injective,
    totalDegree_map_of_injective Int.cast_injective] at hbezout
  exact (by exact_mod_cast hbezout : (S.card : ℝ) ≤ f.totalDegree * (g.totalDegree : ℝ)).trans
    (mul_le_mul_of_nonneg_left hgdeg (Nat.cast_nonneg _))

private lemma plane_auxiliary_expression (d : ℕ) (B L b : ℝ) :
    affineAuxiliaryDegreeExpression 0 d B L b =
      (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) *
        (min (1 + Real.log B / d) (b / L ^ (1 / ((d : ℝ) * d))) + 2) := by
  norm_num [affineAuxiliaryDegreeExpression, auxDegreeScale, heightExponent, degreeRoot, Real.rpow_ofNat]

private theorem affine_plane_expression_le_bad_prime (d : ℕ)
    {B L b : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineAuxiliaryDegreeExpression 0 d B L b ≤
      (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (b + 2) := by
  rw [plane_auxiliary_expression]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := div_le_self hb (Real.one_le_rpow hL (show 0 ≤ 1 / ((d : ℝ) * d) by positivity))
  linarith only [h, min_le_right (1 + Real.log B / d) (b / L ^ (1 / ((d : ℝ) * d)))]

/-- A logarithm-free count with the bad-prime factor kept explicit. -/
theorem affine_plane_count_bad_prime
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      affineHypersurfaceAuxiliaryConstant 0 * (f.totalDegree : ℝ) ^ 4 *
        (hypersurfaceBadPrimeFactor f + 2) * B ^ (1 / (f.totalDegree : ℝ)) := by
  apply (affine_plane_count_le_auxiliary_expression f hprim hir hd hB).trans
  have h := affine_plane_expression_le_bad_prime f.totalDegree hB (leading_height_one_le f
    (ne_zero_of_irreducible_map hir)) (hypersurfaceBadPrimeFactor_nonneg f)
  have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h
    (affineHypersurfaceAuxiliaryConstant_pos 0).le) (Nat.cast_nonneg (α := ℝ) f.totalDegree)
  convert h' using 1
  ring

private theorem affine_plane_expression_le_uniform {d : ℕ} (hd : 0 < d)
    {B L b : ℝ} (hB : 1 ≤ B) :
    affineAuxiliaryDegreeExpression 0 d B L b ≤
      3 * (d : ℝ) ^ 2 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog := Real.log_nonneg hB
  rw [plane_auxiliary_expression]
  calc
    _ ≤ (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (3 * (1 + Real.log B / d)) := by
      gcongr
      linarith [min_le_left (1 + Real.log B / d) (b / L ^ (1 / ((d : ℝ) * d))),
        show 0 ≤ Real.log B / d by positivity]
    _ = _ := by field_simp; ring

/-- The coefficient-independent constant for rational affine plane curves. -/
def affinePlaneCountConstant : ℝ := 3 * affineHypersurfaceAuxiliaryConstant 0

lemma affinePlaneCountConstant_pos : 0 < affinePlaneCountConstant :=
  mul_pos (by norm_num) (affineHypersurfaceAuxiliaryConstant_pos 0)

/-- The coefficient-uniform plane-curve bound, including nonabsolute equations. -/
theorem affine_plane_equation_bound (f : MvPolynomial (Fin 2) ℚ) (hir : Irreducible f)
    (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤ affinePlaneCountConstant * curveBound f.totalDegree B := by
  obtain ⟨g, hprim, ha⟩ := exists_primitive_integer_model f hir.ne_zero
  have hirg := ha.irreducible hir
  have hzero : zeroLocus (map (Int.castRingHom ℚ) g) = zeroLocus f :=
    Set.ext (rational_model_zero_iff ha)
  have hdeg := rational_model_degree ha hir.ne_zero
  have hdg : 0 < g.totalDegree := hdeg ▸ hd
  have h := affine_plane_count_le_auxiliary_expression g hprim hirg hdg hB
  rw [← hzero, ← hdeg]
  apply h.trans
  have h' := affine_plane_expression_le_uniform (b := hypersurfaceBadPrimeFactor g)
    (L := integerCoefficientHeight (homogeneousComponent g.totalDegree g)) hdg hB
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h'
    (affineHypersurfaceAuxiliaryConstant_pos 0).le) (Nat.cast_nonneg (α := ℝ) g.totalDegree)
  unfold affinePlaneCountConstant curveBound
  convert hm using 1
  ring

/-- The plane case of CCDN Theorem 3. -/
theorem planeCurveBound : PlaneCurveBound :=
  ⟨affinePlaneCountConstant, affinePlaneCountConstant_pos, fun f hf hd _ hB =>
    affine_plane_equation_bound f hf hd hB⟩

end
end CCDN
