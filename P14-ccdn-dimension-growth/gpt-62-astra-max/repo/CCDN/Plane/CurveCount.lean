/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Statements
public import CCDN.Plane.AffinePlaneBadPrimeCount
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ScaledHypersurfaceHeight

/-! In dimension one, the coefficient-sensitive auxiliary gives two estimates. The
right side of the minimum gives `affine_plane_count_bad_prime`. Here we use the
left side: height transfer bounds the logarithm of the leading height divided by
its small positive power, independently of the height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem plane_curve_count (f : CoordinatePolynomial 2) (hf : Irreducible f)
    {B : ℝ} (hB : 1 ≤ B) : (count (zeroLocus f) B : ℝ) ≤
      (2 * affineHypersurfaceAuxiliaryConstant 0) * curveBound f.totalDegree B := by
  have hC := affineHypersurfaceAuxiliaryConstant_pos 0
  obtain ⟨g, a, hg, ha, he, hir⟩ := primitive_model_irreducible hf
  have hz : zeroLocus (rationalEquation g) = zeroLocus f := Set.ext (rational_scalar_model_zero_iff ha he)
  have h := primitive_eqn_count_le_aux hg hir hB (min_le_right _ _)
  rw [hz, (rational_scalar_model_degree ha hf.ne_zero he)] at h
  have hd := by exact_mod_cast totalDegree_pos_of_irreducible hf
  apply h.trans
  unfold curveBound
  field_simp
  linarith [Real.log_nonneg hB]

/-- The coefficient-uniform plane curve bound. -/
theorem planeCurveBound : PlaneCurveBound :=
  ⟨_, mul_pos (by norm_num) (affineHypersurfaceAuxiliaryConstant_pos 0),
    fun f hf _ _ hB => plane_curve_count f hf hB⟩

end
end CCDN
