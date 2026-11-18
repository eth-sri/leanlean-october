/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
public import CCDN.Height.ProjectiveZeroLocus
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Algebra.PrimitiveNormalization
import CCDN.Plane.ProjectivePlaneBezout

/-! Uniform CCDN Theorem 2 for rational projective plane equations in every positive degree,
obtained from the `n = 0` specialization of `hypersurface_projective_auxiliary` and Bézout. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Explicit constant for the uniform projective plane curve bound. -/
def projectivePlaneAbsoluteConstant : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant 0 *
    (Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant 3 + 2)

/-- The constant `projectivePlaneAbsoluteConstant` is positive. -/
lemma projectivePlaneAbsoluteConstant_pos : 0 < projectivePlaneAbsoluteConstant := by
  unfold projectivePlaneAbsoluteConstant
  have := hypersurfaceAbsoluteAuxiliaryConstant_pos 0
  have := zero_lt_one.trans_le (hypersurfaceHeightConstant_one_le 3)
  positivity

private lemma auxDegreeBound_zero_le {d : ℕ} (hd : 0 < d) (g : MvPolynomial (Fin 3) ℤ)
    (hgd : g.totalDegree = d) (hg0 : g ≠ 0) {B : ℝ} (hB : 1 ≤ B) :
    hypersurfaceAuxiliaryDegreeBound 0 d B (hypersurfaceBadPrimeFactor g)
      (integerCoefficientHeight g) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 3 * B ^ (2 / (d : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hd1
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  set H : ℝ := (integerCoefficientHeight g : ℝ)
  have hH1 : 1 ≤ H := by
    dsimp only [H]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (integerCoefficientHeight_pos g hg0).ne'
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  set K₀ : ℝ := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant 3
  have hK₀ : 0 < K₀ := by
    dsimp only [K₀]
    have := zero_lt_one.trans_le (hypersurfaceHeightConstant_one_le 3)
    positivity
  have hb := hypersurfaceBadPrimeFactor_le_height g H hH1
    (coefficient_abs_le_integerCoefficientHeight g)
  rw [hgd] at hb
  set u := H ^ (1 / (d : ℝ) ^ 2)
  have hu0 : 0 < u := Real.rpow_pos_of_pos hH0 _
  have hratio : (1 + Real.log H / (d : ℝ) ^ 2) / u ≤ 1 := by
    rw [div_le_one hu0]
    have hl : Real.log u = Real.log H / (d : ℝ) ^ 2 := by
      rw [Real.log_rpow hH0]; ring
    linarith [Real.log_le_sub_one_of_pos hu0]
  have hBpow : 1 ≤ B ^ (2 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have hmain : auxMainTerm 0 d B (hypersurfaceBadPrimeFactor g) H ≤
      K₀ * (d : ℝ) ^ 3 * B ^ (2 / (d : ℝ)) := by
    unfold auxMainTerm boxExponent heightExponent degreeRoot
    norm_num only [Nat.cast_zero, zero_add, div_one, Real.rpow_one, one_mul,
      show (4 - 1 : ℝ) = 3 by norm_num, Real.rpow_ofNat]
    rw [show 1 / ((d : ℝ) * d) = 1 / (d : ℝ) ^ 2 by ring]
    change (d : ℝ) ^ 3 * hypersurfaceBadPrimeFactor g * B ^ (2 / (d : ℝ)) / u ≤ _
    calc (d : ℝ) ^ 3 * hypersurfaceBadPrimeFactor g * B ^ (2 / (d : ℝ)) / u
        ≤ (d : ℝ) ^ 3 * (K₀ * (1 + Real.log H / (d : ℝ) ^ 2)) * B ^ (2 / (d : ℝ)) / u := by
          gcongr
      _ = K₀ * (d : ℝ) ^ 3 * B ^ (2 / (d : ℝ)) * ((1 + Real.log H / (d : ℝ) ^ 2) / u) := by ring
      _ ≤ K₀ * (d : ℝ) ^ 3 * B ^ (2 / (d : ℝ)) * 1 := by gcongr
      _ = _ := mul_one _
  have hlogB : Real.log B ≤ (d : ℝ) ^ 3 * B ^ (2 / (d : ℝ)) := by
    have h1 : Real.log (B ^ (2 / (d : ℝ))) = 2 / (d : ℝ) * Real.log B := Real.log_rpow hB0 _
    have h2 : Real.log (B ^ (2 / (d : ℝ))) ≤ B ^ (2 / (d : ℝ)) :=
      Real.log_le_self (by positivity)
    rw [h1, div_mul_eq_mul_div, div_le_iff₀ hd0] at h2
    have hd3 : (d : ℝ) ≤ 2 * (d : ℝ) ^ 3 := by
      have : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
        simpa only [pow_one] using pow_le_pow_right₀ hd1 (by omega : 1 ≤ 3)
      linarith
    have hm := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hm2 := mul_le_mul_of_nonneg_right hd3 (show 0 ≤ B ^ (2 / (d : ℝ)) by positivity)
    nlinarith
  have hd3B : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 3 * B ^ (2 / (d : ℝ)) :=
    le_mul_of_one_le_right (by positivity) hBpow
  unfold hypersurfaceAuxiliaryDegreeBound auxDegreeBound projectivePlaneAbsoluteConstant
  norm_num only [Nat.cast_zero, zero_add, div_one, sub_self, Real.rpow_zero, one_mul,
    show (4 - 1 : ℝ) = 3 by norm_num, Real.rpow_ofNat]
  have hsum : auxMainTerm 0 d B (hypersurfaceBadPrimeFactor g) H + Real.log B + (d : ℝ) ^ 3 ≤
      (K₀ + 2) * (d : ℝ) ^ 3 * B ^ (2 / (d : ℝ)) := by
    dsimp only [K₀] at hmain ⊢; linarith
  exact (mul_le_mul_of_nonneg_left hsum (hypersurfaceAbsoluteAuxiliaryConstant_pos 0).le).trans_eq
    (by dsimp only [K₀]; ring)

/-- Uniform CCDN Theorem 2 for rational projective plane equations,
in every positive degree and for every real `B ≥ 1`. -/
theorem projective_plane_equation_bound {d : ℕ}
    (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible f) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  classical
  obtain ⟨g₀, a, hprim, ha, he⟩ := exists_primitive_integer_model f hir.ne_zero
  have hgh := rational_scalar_model_homogeneous he hf
  have hg0_irQ : Irreducible (map (Int.castRingHom ℚ) g₀) := by
    rw [he]
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr ha).map C)).mpr hir
  have hgir : Irreducible g₀ := hprim.irreducible_of_rational_map hg0_irQ
  have hgd : g₀.totalDegree = d := hgh.totalDegree hgir.ne_zero
  have hzero : projectiveZeroLocus (map (Int.castRingHom ℚ) g₀) = projectiveZeroLocus f :=
    Set.ext fun x => rational_scalar_model_zero_iff ha he x.rep
  obtain ⟨M, hM, G, _, hGhom, hGzero, hGnd⟩ :=
    hypersurface_projective_auxiliary g₀ hgh hd hgir hB
  have hndQ : ¬ map (Int.castRingHom ℚ) g₀ ∣ map (Int.castRingHom ℚ) G :=
    fun h => hGnd (hprim.rational_map_dvd_iff.mp h)
  let S := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) g₀)) B
  have hbez := projective_plane_common_zeros_card_le (map (Int.castRingHom ℚ) g₀)
    (map (Int.castRingHom ℚ) G) (hgh.map _) hg0_irQ (hGhom.map _) hndQ
    (fun x : S => x.val) Subtype.val_injective
    (fun x => (mem_projectivePoints.mp x.property).2)
    (fun x => hGzero x.val (mem_projectivePoints.mp x.property).1
      (mem_projectivePoints.mp x.property).2)
  rw [Fintype.card_coe] at hbez
  rw [← hzero]
  have hcard : (projectiveCount (projectiveZeroLocus (map (Int.castRingHom ℚ) g₀)) B : ℝ) ≤
      (d : ℝ) * M := by exact_mod_cast hbez
  have hM' := hM.trans (auxDegreeBound_zero_le hd g₀ hgd hgir.ne_zero hB)
  exact (hcard.trans (mul_le_mul_of_nonneg_left hM' (Nat.cast_nonneg _))).trans_eq (by ring)

end
end CCDN
