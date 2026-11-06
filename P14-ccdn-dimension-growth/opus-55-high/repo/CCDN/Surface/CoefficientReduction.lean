/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Height.Box
import CCDN.Height.IntegerCoefficientHeight
import CCDN.Height.PrimitiveIntegerPolynomial
import CCDN.Hilbert.AffineCurveDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.Hypersurface.NonabsoluteSurfaceCount
import CCDN.Surface.CompleteIntersectionDegreeBudget

/-! Coefficients of a primitive surface equation can be restricted to
polynomial height in the box radius. The complementary case already has
a linear point bound from a degree-at-most-d auxiliary. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {B : ℝ}

theorem surface_section_count_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (hB : 0 ≤ B) :
    (count (zeroLocus f ∩ zeroLocus g) B : ℝ) ≤
      (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) := by
  obtain ⟨S, δ, hcurve, hcover, hbudget⟩ :=
    exists_completeIntersection_curve_components f g hf hfg
  rw [hcover]
  have hsum : (∑ P ∈ S, (δ P : ℝ)) ≤
      (f.totalDegree : ℝ) * g.totalDegree := mod_cast hbudget
  exact (finite_curve_union_count_le_box_side S δ (fun P hP =>
    ⟨(hcurve P hP).isPrime, (hcurve P hP).height_eq, (hcurve P hP).degree⟩) hB).trans
      (mul_le_mul_of_nonneg_right hsum (by linarith))

end

section
variable (d : ℕ)

/-- The constant `N (log N + d) + 1`, where `N = binom(d + 3, d)` is the number of monomials of
degree at most `d` in three variables, in the logarithmic coefficient-height bound for primitive
surface equations of degree `d`. -/
def surfaceCoefficientLogConstant : ℝ :=
  ((3 + d).choose d : ℝ) * (Real.log ((3 + d).choose d) + d) + 1

end

/-- The alternative to controlled coefficient height is already O(d²B).
The height constant depends on the degree alone. -/
theorem primitive_surface_coefficient_reduction
    (f : MvPolynomial (Fin 3) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hf : Irreducible (map (Int.castRingHom ℚ) f))
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      surfaceCoefficientLogConstant f.totalDegree * (Real.log B + 1) ∨
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      3 * (f.totalDegree : ℝ) ^ 2 * B := by
  rcases affine_coefficient_height_dichotomy f (by aesop) hprim hB with
    hheight | ⟨g, ⟨_, hproper, hzero⟩, hdeg⟩
  · left
    have hlog := Real.log_nonneg hB
    have hNlog' : (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((3 + f.totalDegree).choose f.totalDegree) := by positivity
    unfold surfaceCoefficientLogConstant
    nlinarith
  · right
    have hproperQ :=
      fun h => hproper (hprim.rational_map_dvd_iff.mp h)
    have hcount : (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) := by
      have hcount : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
          count (zeroLocus (map (Int.castRingHom ℚ) f) ∩
            zeroLocus (map (Int.castRingHom ℚ) g)) B := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨hxB, hxf⟩ := mem_integralPoints.mp hx
        exact mem_integralPoints.mpr ⟨hxB, hxf, (by
          have hh := congrArg (Int.castRingHom ℚ) (hzero x hxB (by
            apply (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
            rwa [map_zero, map_eval]))
          rwa [map_eval, map_zero] at hh)⟩
      have hbound := surface_section_count_le (map (Int.castRingHom ℚ) f)
        (map (Int.castRingHom ℚ) g) hf hproperQ (show 0 ≤ B by linarith)
      rw [rational_map_totalDegree, rational_map_totalDegree] at hbound
      exact le_trans (mod_cast hcount) hbound
    calc
      _ ≤ f.totalDegree * g.totalDegree * (2 * B + 1) := hcount
      _ ≤ f.totalDegree * f.totalDegree * (3 * B) := by
        gcongr
        linarith
      _ = _ := by ring

