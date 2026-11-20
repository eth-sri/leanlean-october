/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.Plane.Bezout
import CCDN.Hypersurface.NonabsoluteHypersurfaceCount

/-! A logarithm-free plane-curve estimate in terms of the
geometric bad-prime factor. Uniformly bounded bad-prime factors therefore
give a coefficient-independent logarithm-free counting theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Apply Bézout to a plane curve and its general affine auxiliary. -/
lemma primitive_eqn_count_le_aux {f : IntegerPolynomial 2}
    (hprim : PrimitiveIntegerPolynomial f) (hir : Irreducible (rationalEquation f))
    {B A : ℝ} (hB : 1 ≤ B) (hA : affineAuxiliaryCharge 0 f.totalDegree B
      (integerCoefficientHeight (homogeneousComponent f.totalDegree f)) (hypersurfaceBadPrimeFactor f) ≤ A) :
    (count (zeroLocus (rationalEquation f)) B : ℝ) ≤
      affineHypersurfaceAuxiliaryConstant 0 * (f.totalDegree : ℝ)^4 * B^(1 / (f.totalDegree : ℝ)) * (A + 1) := by
  have hd := MvPolynomial.totalDegree_pos_of_irreducible hir
  rw [rational_map_totalDegree] at hd
  by_cases habs : AbsolutelyIrreducible f
  case neg =>
    have hc := nonabsolute_hypersurface_dimension_growth (rationalEquation f) hir
      (fun h => habs ((absolutelyIrreducibleRat_map_iff f).mp h)) hB
    simp only [pow_zero,one_mul,mul_one,rational_map_totalDegree] at hc
    have hA0 : 0 ≤ A := le_trans (le_min (by have := hypersurfaceBadPrimeFactor_nonneg f; positivity)
      (by have := Real.log_nonneg hB; positivity)) hA
    have hC : 1 ≤ affineHypersurfaceAuxiliaryConstant 0 := by
      unfold affineHypersurfaceAuxiliaryConstant scalingCost
      have := hypersurfaceAbsoluteAuxiliaryConstant_one_le 0
      have := scalingHeightCost_one_le 0
      have := Real.one_le_exp (by positivity : (0:ℝ) ≤ 0+1)
      apply one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by assumption) (by linarith))
      apply one_le_mul_of_one_le_of_one_le (by norm_num); exact Real.one_le_exp (by positivity)
    have hd1 : (1:ℝ) ≤ f.totalDegree := by exact_mod_cast hd
    apply hc.trans
    calc (f.totalDegree:ℝ)^2 = 1*(f.totalDegree:ℝ)^2*1*1 := by ring
         _ ≤ _ := by gcongr <;> first | apply Real.one_le_rpow hB (by positivity) | omega | linarith
  obtain ⟨g, ⟨_, hnd, hz⟩, hdeg⟩ :=
    affine_hypersurface_auxiliary f hprim habs hd hB hA
  classical
  let S := integralPoints (zeroLocus (rationalEquation f)) B
  have hs (x : S) := mem_integralPoints.mp x.property
  have hcount := plane_common_zeros_card_le _ (rationalEquation g) hir (fun h => hnd (hprim.rational_map_dvd_iff.mp h))
    (fun x : S => rationalPoint x.val) ((rationalPoint_injective 2).comp Subtype.val_injective)
    (fun x => (hs x).2) (fun x => by
      rw [eval_rationalPoint_map, Int.cast_eq_zero]
      apply hz x.val (hs x).1
      have h : eval (rationalPoint x.val) (rationalEquation f) = 0 := (hs x).2
      simpa only [eval_rationalPoint_map, Int.cast_eq_zero] using h)
  rw [Fintype.card_coe, rational_map_totalDegree, rational_map_totalDegree] at hcount
  apply (Nat.cast_le.mpr hcount).trans
  push_cast
  have h := mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg (α := ℝ) f.totalDegree)
  norm_num [auxDegreeScale, affineBoxPower, degreeRoot] at h
  convert h using 1; ring

/-- The plane auxiliary and Bezout prove the bad-prime bound for
integer zeros. -/
theorem affine_plane_count_bad_prime
    (f : IntegerPolynomial 2) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (rationalEquation f))
    (_hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (rationalEquation f)) B : ℝ) ≤
      affineHypersurfaceAuxiliaryConstant 0 * (f.totalDegree : ℝ) ^ 4 *
        (hypersurfaceBadPrimeFactor f + 2) * B ^ (1 / (f.totalDegree : ℝ)) := by
  have hL := leading_height_one_le f (ne_zero_of_irreducible_map hir)
  have hcharge : affineAuxiliaryCharge 0 f.totalDegree B _ (hypersurfaceBadPrimeFactor f) ≤ hypersurfaceBadPrimeFactor f :=
    (min_le_left _ _).trans (div_le_self (hypersurfaceBadPrimeFactor_nonneg _) (Real.one_le_rpow hL (by positivity)))
  have h := primitive_eqn_count_le_aux hprim hir hB (hcharge.trans (le_add_of_nonneg_right zero_le_one))
  convert h using 1; ring

end
end CCDN
