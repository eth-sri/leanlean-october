/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.ProjectiveZeroLocus
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.Plane.ProjectivePlaneBezout

/-! Specialize the hypersurface auxiliary theorem to plane curves and apply
projective Bézout. In dimension one, the coefficient-height exponent `1/d²`
absorbs the entire bad-prime factor. -/

public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The absolute constant in the projective plane-curve estimate. -/
def projectivePlaneAbsoluteConstant : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant 0 * (badPrimeHeightConstant 0 2 + 2)

lemma projectivePlaneAbsoluteConstant_pos : 0 < projectivePlaneAbsoluteConstant := by
  exact mul_pos (hypersurfaceAbsoluteAuxiliaryConstant_pos 0)
    (by linarith [badPrimeHeightConstant_nonneg 0 2])

private lemma plane_auxiliary_degree_le {d : ℕ} (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    hypersurfaceAuxiliaryDegreeBound 0 d B (hypersurfaceBadPrimeFactor f)
        (integerCoefficientHeight f) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 3 * B ^ (2 / (d : ℝ)) := by
  have hH : (1 : ℝ) ≤ integerCoefficientHeight f := Nat.one_le_cast.mpr (integerCoefficientHeight_pos f hf0)
  have hbad := hypersurface_badPrime_height_transfer (n := 0) f (hf.totalDegree hf0) hd le_rfl hH
  simp only [Real.log_one, zero_div, add_zero, Real.one_rpow, div_one, mul_one] at hbad
  have hbox : boxExponent 0 d = 2 / (d : ℝ) := by norm_num [boxExponent, degreeRoot]
  have hscale : auxDegreeScale 0 d = (d : ℝ) ^ 3 := by norm_num [auxDegreeScale, Real.rpow_ofNat]
  have hexp : 1 / degreeRoot 0 d ≤ boxExponent 0 d := by
    rw [hbox]
    norm_num only [degreeRoot, Nat.cast_zero, zero_add, div_one, Real.rpow_one]
    gcongr
    norm_num
  let Q := auxDegreeScale 0 d * B ^ boxExponent 0 d
  let K := badPrimeHeightConstant 0 2
  have hmain : auxMainTerm 0 d B (hypersurfaceBadPrimeFactor f) (integerCoefficientHeight f) ≤ Q * K := by
    unfold auxMainTerm
    gcongr
  have hrest := auxDegree_remainder_le hd hB hexp
  unfold hypersurfaceAuxiliaryDegreeBound projectivePlaneAbsoluteConstant
  rw [← hbox, ← hscale, mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos 0).le
  change auxMainTerm 0 d B _ _ + auxLogTerm 0 d B + auxDegreeScale 0 d ≤ (K + 2) * Q
  linarith only [hmain, hrest]

/-- Uniform CCDN Theorem 2 for rational projective plane equations, including
linear and geometrically reducible equations. -/
theorem projective_plane_equation_bound {d : ℕ}
    (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible f) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  classical
  obtain ⟨g, hprim, ha⟩ := exists_primitive_integer_model f hir.ne_zero
  have hg := rational_model_homogeneous ha hf
  have hgQ := ha.irreducible hir
  have hirg := hprim.irreducible_of_rational_map hgQ
  obtain ⟨M, hM, G, _, hG, hGzero, hGnd⟩ := hypersurface_projective_auxiliary g hg hd hirg hB
  have hzero : projectiveZeroLocus (map (Int.castRingHom ℚ) g) = projectiveZeroLocus f :=
    Set.ext fun x => rational_model_zero_iff ha x.rep
  let S := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) g)) B
  have hmem (x : S) := mem_projectivePoints.mp x.property
  have hc := projective_plane_common_zeros_card_le _ _ (hg.map _) hgQ (hG.map _)
    (fun h => hGnd (hprim.rational_map_dvd_iff.mp h)) (fun x : S => x.val) Subtype.val_injective
    (fun x => (hmem x).2) (fun x => hGzero x (hmem x).1 (hmem x).2)
  have hcount : (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤ d * (M : ℝ) := by
    rw [← hzero]
    exact_mod_cast (by simpa only [Fintype.card_coe] using hc : S.card ≤ d * M)
  have hdeg := hM.trans (plane_auxiliary_degree_le g hg hirg.ne_zero hd hB)
  convert hcount.trans (mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg d)) using 1
  ring

end
end CCDN
