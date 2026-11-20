/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.Height.PrimitiveIntegerPolynomial
public import CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Algebra.FieldMapIrreducible
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.Hypersurface.NonabsoluteHypersurfaceCount

/-! Coefficients of a primitive surface equation can be restricted to
polynomial height in the box radius. The complementary case already has
a linear point bound from a degree-at-most-d auxiliary. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable (f : IntegerPolynomial 3) (d : ℕ)

/-- The constant `N (log N + d) + 1`, where `N = binom(d + 3, d)` is the number of monomials of
degree at most `d` in three variables, in the logarithmic coefficient-height bound for primitive
surface equations of degree `d`. -/
def surfaceCoefficientLogConstant : ℝ :=
  ((3 + d).choose d : ℝ) * (Real.log ((3 + d).choose d) + d) + 1

/-- The coefficient-height constant `surfaceCoefficientLogConstant d` is positive. -/
theorem surfaceCoefficientLogConstant_pos :
    0 < surfaceCoefficientLogConstant d := by
  unfold surfaceCoefficientLogConstant
  positivity

/-- The alternative to controlled coefficient height is already O(d²B).
The height constant depends on the degree alone. -/
theorem primitive_surface_coefficient_reduction (hprim : PrimitiveIntegerPolynomial f)
    (hf : Irreducible (rationalEquation f))
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      surfaceCoefficientLogConstant f.totalDegree * (Real.log B + 1) ∨
    (count (zeroLocus (rationalEquation f)) B : ℝ) ≤
      9 * (f.totalDegree : ℝ) ^ 2 * B := by
  have hf0 : f ≠ 0 := by intro h; exact hf.ne_zero (by rw [h, map_zero])
  rcases affine_coefficient_height_dichotomy f hf0 hprim hB with
    hheight | ⟨g, ⟨_, hproper, hzero⟩, hdeg⟩
  · left
    have hlog := Real.log_nonneg hB
    have hNlog := Real.log_natCast_nonneg ((3 + f.totalDegree).choose f.totalDegree)
    have hNlog' : (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((3 + f.totalDegree).choose f.totalDegree) := by positivity
    unfold surfaceCoefficientLogConstant
    nlinarith
  · right
    have hc := proper_intersection_count_le_box (n:=1) (rationalEquation f) (rationalEquation g) hf.prime
      (fun h => hproper (hprim.rational_map_dvd_iff.mp h)) (rational_map_totalDegree f).le ((rational_map_totalDegree g).le.trans hdeg) (show 0 ≤ B by linarith)
    have hs : count (zeroLocus (rationalEquation f)) B ≤ count (zeroLocus (rationalEquation f) ∩ zeroLocus (rationalEquation g)) B :=
      count_le_of_box_imp fun x hx ht => ⟨ht,mem_integer_zeroLocus.mpr (hzero x hx (mem_integer_zeroLocus.mp ht))⟩
    norm_num at hc
    apply (Nat.cast_le (α:=ℝ)).mpr hs |>.trans (hc.trans ?_)
    nlinarith [mul_le_mul_of_nonneg_right hB (sq_nonneg (f.totalDegree:ℝ))]

end
end CCDN
