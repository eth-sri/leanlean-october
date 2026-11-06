/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.Height.PrimitiveIntegerPolynomial
public import CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.Hypersurface.NonabsoluteSurfaceCount
import CCDN.Surface.CompleteIntersectionDegreeBudget

/-! Coefficients of a primitive surface equation can be restricted to
polynomial height in the box radius. The complementary case already has
a linear point bound from a degree-at-most-d auxiliary. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The constant `N (log N + d) + 1`, where `N = binom(d + 3, d)` is the number of monomials of
degree at most `d` in three variables, in the logarithmic coefficient-height bound for primitive
surface equations of degree `d`. -/
def surfaceCoefficientLogConstant (d : ℕ) : ℝ :=
  ((3 + d).choose d : ℝ) * (Real.log ((3 + d).choose d) + d) + 1

/-- The coefficient-height constant `surfaceCoefficientLogConstant d` is positive. -/
theorem surfaceCoefficientLogConstant_pos (d : ℕ) :
    0 < surfaceCoefficientLogConstant d := by
  have hh := Real.log_natCast_nonneg ((3 + d).choose d)
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
      3 * (f.totalDegree : ℝ) ^ 2 * B := by
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by rw [h, map_zero])
  rcases affine_coefficient_height_dichotomy f hf0 hprim hB with
    hheight | ⟨g, ⟨_, hproper, hzero⟩, hdeg⟩
  · left
    have hlog := Real.log_nonneg hB
    have hNlog := Real.log_natCast_nonneg ((3 + f.totalDegree).choose f.totalDegree)
    have hNd : (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) * f.totalDegree := by
      positivity
    have hNlog' : (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((3 + f.totalDegree).choose f.totalDegree) := by positivity
    unfold surfaceCoefficientLogConstant
    nlinarith
  · right
    have hproperQ : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g :=
      fun h => hproper (hprim.rational_map_dvd_iff.mp h)
    have hsub : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
        count (zeroLocus (map (Int.castRingHom ℚ) f) ∩
          zeroLocus (map (Int.castRingHom ℚ) g)) B :=
      Finset.card_le_card fun x hx => by
        obtain ⟨hxB, hxf⟩ := mem_integralPoints.mp hx
        have hf0 : eval x f = 0 := by
          apply (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
          rw [map_zero, map_eval]; exact hxf
        have hg0 : eval (rationalPoint x) (map (Int.castRingHom ℚ) g) = 0 := by
          have hh := congrArg (Int.castRingHom ℚ) (hzero x hxB hf0)
          rw [map_eval, map_zero] at hh; exact hh
        exact mem_integralPoints.mpr ⟨hxB, hxf, hg0⟩
    obtain ⟨S, δ, hcurve, hcover, hbudget, _⟩ :=
      exists_completeIntersection_curve_components _ _ hf hproperQ
    have hsum : (∑ P ∈ S, (δ P : ℝ)) ≤ (f.totalDegree : ℝ) * g.totalDegree := by
      simpa only [rational_map_totalDegree] using (by exact_mod_cast hbudget :
        (∑ P ∈ S, (δ P : ℝ)) ≤ ((map (Int.castRingHom ℚ) f).totalDegree : ℝ) *
          (map (Int.castRingHom ℚ) g).totalDegree)
    have hsubR : (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        count (zeroLocus (map (Int.castRingHom ℚ) f) ∩
          zeroLocus (map (Int.castRingHom ℚ) g)) B := by exact_mod_cast hsub
    have hcount : (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) := by
      refine hsubR.trans ?_
      rw [hcover]
      exact (finite_curve_union_count_le_box_side S δ (fun P hP =>
        ⟨(hcurve P hP).isPrime, (hcurve P hP).height_eq, (hcurve P hP).degree⟩)
        (by linarith)).trans (mul_le_mul_of_nonneg_right hsum (by linarith))
    have hdegR : (g.totalDegree : ℝ) ≤ f.totalDegree := mod_cast hdeg
    calc
      _ ≤ (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) := hcount
      _ ≤ (f.totalDegree : ℝ) * f.totalDegree * (3 * B) := by gcongr; linarith
      _ = _ := by ring

end
end CCDN
