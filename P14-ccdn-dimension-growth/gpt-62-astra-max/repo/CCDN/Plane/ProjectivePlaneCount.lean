/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
public import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.Algebra.PrimitiveNormalization
import CCDN.Plane.ProjectivePlaneBezout

/-! The projective auxiliary in dimension one and homogeneous Bézout give the
plane curve bound directly, in all degrees and without a geometric irreducibility assumption. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The dimension-one height error in the determinant lower bound. -/
def planeHeightCost := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant 3

def projectivePlaneAbsoluteConstant := hypersurfaceAbsoluteAuxiliaryConstant 0 * (planeHeightCost + 2)

lemma projectivePlaneAbsoluteConstant_pos : 0 < projectivePlaneAbsoluteConstant := by
  have := hypersurfaceHeightConstant_one_le 3
  have := hypersurfaceAbsoluteAuxiliaryConstant_pos 0
  unfold projectivePlaneAbsoluteConstant planeHeightCost
  positivity

private lemma plane_aux_degree_bound {d} (f : IntegerPolynomial 3) (hf : f ≠ 0)
    (hdeg : f.totalDegree = d) (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    hypersurfaceAuxiliaryDegreeBound 0 d B (hypersurfaceBadPrimeFactor f) (integerCoefficientHeight f) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ)^3 * B^(2 / (d : ℝ)) := by
  let Q := B ^ (2 / (d : ℝ))
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hr : hypersurfaceBadPrimeFactor f / (integerCoefficientHeight f : ℝ)^heightExponent 0 d ≤
      planeHeightCost := by simpa [heightExponent, degreeRoot, planeHeightCost] using (hypersurface_badPrime_fractional_height_bound f hf hdeg (r := 1) (by decide) hd)
  have hlog : Real.log B ≤ (d : ℝ)^3 * Q := calc
    _ ≤ B^(2 / (d : ℝ)) / (2 / d) := Real.log_le_rpow_div (by linarith) (by positivity)
    _ = (d / 2) * Q := by dsimp [Q]; field_simp
    _ ≤ _ := by gcongr; nlinarith only [hd1, mul_nonneg (sq_nonneg (d : ℝ)) (sub_nonneg.mpr hd1), sq_nonneg (d-1)]
  have hpow := le_mul_of_one_le_right (by positivity : 0 ≤ (d : ℝ)^3) hQ
  have hmain := mul_le_mul_of_nonneg_left hr (show 0 ≤ d^3 * Q by positivity)
  unfold hypersurfaceAuxiliaryDegreeBound auxDegreeBound auxMainTerm projectivePlaneAbsoluteConstant
  conv_rhs => simp only [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos 0).le
  norm_num only [Nat.cast_zero, zero_add, div_one, Real.rpow_one, Real.rpow_zero, one_mul, sub_self,
    show (4 - 1) = 3 by norm_num, Real.rpow_ofNat, boxExponent, degreeRoot]
  grind

/-- Bézout applied to the general projective auxiliary in dimension one. -/
theorem projective_plane_equation_bound {d : ℕ} (f : CoordinatePolynomial 3) (hf : f.IsHomogeneous d)
    (hd : 0 < d) (hir : Irreducible f) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ)^4 * B^(2 / (d : ℝ)) := by
  classical
  obtain ⟨F, a, hprim, ha, he, hF⟩ := primitive_model_irreducible hir
  have hhom := rational_scalar_model_homogeneous he hf
  have hF0 := ne_zero_of_irreducible_map hF
  obtain ⟨M, hM, g, _, hg, hvan, hnd⟩ :=
    hypersurface_projective_auxiliary F hhom hd (hprim.irreducible_of_rational_map hF) hB
  have hs (x : (projectivePoints (projectiveZeroLocus (rationalEquation F)) B)) := mem_projectivePoints.mp x.property
  have hc := projective_plane_common_zeros_card_le _ (rationalEquation g) (hhom.map _) hF
    (hg.map _) (by solve_by_elim [hprim.rational_map_dvd_iff.mp]) Subtype.val Subtype.val_injective
    (fun x => (hs x).2) (fun x => hvan x.val (hs x).1 (hs x).2)
  have hz : projectiveZeroLocus _ = projectiveZeroLocus f :=
    Set.ext fun x => rational_scalar_model_zero_iff ha he x.rep
  rw [← hz]
  rw [Fintype.card_coe] at hc
  apply (Nat.cast_le.mpr hc).trans
  push_cast
  have h := mul_le_mul_of_nonneg_left (hM.trans (plane_aux_degree_bound F hF0 (hhom.totalDegree hF0) hd hB))
    (Nat.cast_nonneg (α := ℝ) d)
  convert h using 1; ring

end
end CCDN
