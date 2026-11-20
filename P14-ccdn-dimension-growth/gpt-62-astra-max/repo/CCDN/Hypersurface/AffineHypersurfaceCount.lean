/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Hypersurface.HyperplaneSlicingInduction
import CCDN.Algebra.PrimitiveNormalization
import CCDN.Surface.AffineSurfaceDimensionGrowth
import CCDN.Surface.TopFormIrreducibility

/-! Affine hypersurface dimension growth with the corrected degree exponent: the surface bound
`d^18` of Proposition 4.3.4 starts the hyperplane-slicing induction, which costs `d^3` for each
further variable, and clearing denominators passes from integer to rational equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Clearing denominators transfers affine dimension growth from integer equations to
rational equations with the same constant. -/
theorem AffineHypersurfaceGrowth.rational {n e : ℕ} (h : AffineHypersurfaceGrowth n e) :
    RationalAffineHypersurfaceGrowth n e := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun f hir hd B hB => ?_⟩
  have hf : f ≠ 0 := by aesop
  obtain ⟨g, r, _, hr, he⟩ := exists_primitive_integer_model f hf
  have hdeg := rational_scalar_model_degree hr hf he
  have hz : zeroLocus (rationalEquation g) = zeroLocus f := Set.ext (rational_scalar_model_zero_iff hr he)
  have hi : HasAbsIrreducibleTopForm g := by
    let φ := algebraMap ℚ (AlgebraicClosure ℚ)
    have hmodel := congrArg (map φ) he
    rw [map_map, RingHom.ext_int (φ.comp _), map_mul, map_C] at hmodel
    rw [HasAbsIrreducibleTopForm, AbsolutelyIrreducible, map_homogeneousComponent, hmodel,
      homogeneousComponent_C_mul, hdeg, ← map_homogeneousComponent]
    exact (irreducible_isUnit_mul (((isUnit_iff_ne_zero.mpr hr).map φ).map MvPolynomial.C)).mpr hir
  simpa only [hdeg, hz] using hbound g hi (by omega) B hB

/-- Affine dimension growth with degree exponent `18 + 3 * n` for integer polynomials in `n + 3`
variables of degree at least five with absolutely irreducible top-degree form. -/
theorem affineHypersurfaceGrowth (n : ℕ) : AffineHypersurfaceGrowth n (18 + 3 * n) :=
  affineHypersurfaceGrowth_of_surface (by
    simpa [AffineHypersurfaceGrowth] using affine_surface_dimension_growth) n

end
end CCDN
