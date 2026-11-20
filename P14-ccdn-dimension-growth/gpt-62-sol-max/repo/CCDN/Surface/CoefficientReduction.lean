/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import CCDN.Height.Box
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.Height.PrimitiveIntegerPolynomial
public import CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.AuxiliaryPolynomial.ScaledAffineAuxiliary
import CCDN.Hypersurface.NonabsoluteHypersurfaceCount

/-! Coefficients of a primitive surface equation can be restricted to
polynomial height in the box radius. The complementary case already has
a linear point bound from a degree-at-most-d auxiliary. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem integer_surface_count_le_of_auxiliary
    (f g : MvPolynomial (Fin 3) ℤ)
    (hf : Irreducible (map (Int.castRingHom ℚ) f))
    (hfg : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g)
    (hg : g.totalDegree ≤ f.totalDegree) {B : ℝ} (hB : 1 ≤ B)
    (hzero : ∀ x : IntPoint 3, InBox x B →
      eval x f = 0 → eval x g = 0) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      9 * (f.totalDegree : ℝ) ^ 2 * B := by
  have hh := proper_intersection_count_le (n := 1) (map (Int.castRingHom ℚ) f)
    (map (Int.castRingHom ℚ) g) hf.prime hfg (by simpa only [rational_map_totalDegree] using hg)
    hB (X := zeroLocus (map (Int.castRingHom ℚ) f)) (fun x hx hxf =>
      ⟨hxf, (eval_rationalPoint_map_eq_zero x g).mpr
        (hzero x hx ((eval_rationalPoint_map_eq_zero x f).mp hxf))⟩)
  norm_num [rational_map_totalDegree] at hh
  exact hh

/-- The constant `N (log N + d) + 1`, where `N = binom(d + 3, d)` is the number of monomials of
degree at most `d` in three variables, in the logarithmic coefficient-height bound for primitive
surface equations of degree `d`. -/
def surfaceCoefficientLogConstant (d : ℕ) : ℝ :=
  ((3 + d).choose d : ℝ) * (Real.log ((3 + d).choose d) + d) + 1

/-- The coefficient-height constant `surfaceCoefficientLogConstant d` is positive. -/
theorem surfaceCoefficientLogConstant_pos (d : ℕ) :
    0 < surfaceCoefficientLogConstant d := by
  
  unfold surfaceCoefficientLogConstant
  positivity

/-- The alternative to controlled coefficient height is already O(d²B).
The height constant depends on the degree alone. -/
theorem primitive_surface_coefficient_reduction
    (f : MvPolynomial (Fin 3) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hf : Irreducible (map (Int.castRingHom ℚ) f))
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      surfaceCoefficientLogConstant f.totalDegree * (Real.log B + 1) ∨
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      9 * (f.totalDegree : ℝ) ^ 2 * B := by
  rcases affine_coefficient_height_dichotomy f (by intro h; exact hf.ne_zero (by rw [h, map_zero])) hprim hB with
    hheight | ⟨g, ⟨_, hproper, hzero⟩, hdeg⟩
  · left
    have hlog := Real.log_nonneg hB
    
    
    have hNlog' : (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((3 + f.totalDegree).choose f.totalDegree) := by positivity
    unfold surfaceCoefficientLogConstant
    nlinarith
  · right
    exact integer_surface_count_le_of_auxiliary f g hf (fun h => hproper (hprim.rational_map_dvd_iff.mp h)) hdeg hB hzero

end
end CCDN
