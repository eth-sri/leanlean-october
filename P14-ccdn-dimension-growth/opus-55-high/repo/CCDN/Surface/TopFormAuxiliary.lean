/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.Surface.TopFormAuxiliaryEstimate
import CCDN.Surface.TopFormBadPrimes

/-! A coefficient-uniform auxiliary for an affine hypersurface with absolutely
irreducible leading form. This is the dimension-general form of CCDN (4-3-1). -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable (n : ℕ)

/-- The constant in the degree bound of the auxiliary polynomial for affine hypersurfaces in
`n + 2` variables with absolutely irreducible top-degree form, independent of the
coefficients. -/
def topFormAuxiliaryConstant : ℝ :=
  affineHypersurfaceAuxiliaryConstant n *
    ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 2) + 2)

/-- The auxiliary constant `topFormAuxiliaryConstant n` is positive. -/
lemma topFormAuxiliaryConstant_pos : 0 < topFormAuxiliaryConstant n := by
  have hC := affineHypersurfaceAuxiliaryConstant_pos n
  have hH := zero_le_one.trans (hypersurfaceHeightConstant_one_le (n + 2))
  unfold topFormAuxiliaryConstant
  positivity

end

variable {n : ℕ} (f : MvPolynomial (Fin (n + 2)) ℤ) {B : ℝ}

theorem primitive_top_form_auxiliary
    (hprim : PrimitiveIntegerPolynomial f)
    (hir : HasAbsIrreducibleTopForm f)
    (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ topFormAuxiliaryConstant n *
        (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) *
          B ^ (1 / (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ))) := by
  have hfIr := hprim.irreducible_of_absolute_top hir
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f hir
  have hd := absolute_integer_polynomial_totalDegree_pos f habs
  let d := f.totalDegree
  let F := homogeneousComponent d f
  have hF0 := homogeneousComponent_totalDegree_ne_zero hfIr.ne_zero
  have hFd := (homogeneousComponent_isHomogeneous d f).totalDegree hF0
  let L := (integerCoefficientHeight F : ℝ)
  let q := 1 / ((n + 1 : ℝ) * d * d ^ (1 / (n + 1 : ℝ)))
  let K := (n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 2)
  have hL := leading_height_one_le f hfIr.ne_zero
  have hratio : hypersurfaceBadPrimeFactor f / L ^ q ≤ K := by
    calc
      _ ≤ hypersurfaceBadPrimeFactor F / L ^ q := div_le_div_of_nonneg_right
        (show hypersurfaceBadPrimeFactor f ≤
              hypersurfaceBadPrimeFactor (homogeneousComponent f.totalDegree f) by
            have htop : homogeneousComponent f.totalDegree f ≠ 0 := by
              intro hz
              exact hir.ne_zero (by grind)
            apply hypersurfaceBadPrimeFactor_mono_of_badReduction_imp
            · exact ((homogeneousComponent_isHomogeneous _ _).totalDegree htop).symm
            · grind
            · exact hypersurfaceBadReduction_imp_top_homogeneousComponent f) (by positivity)
      _ ≤ _ := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hypersurface_badPrime_fractional_height_bound F hF0 hFd (r := n + 1) (by omega) hd
  obtain ⟨g, hg, hgdeg⟩ := affine_hypersurface_auxiliary f hprim hfIr hd hB
  refine ⟨g, hg, hgdeg.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left
    (affineAuxiliaryDegreeExpression_le_of_badPrime_ratio n hd hB hL hratio)
    (affineHypersurfaceAuxiliaryConstant_pos n).le
  unfold topFormAuxiliaryConstant
  convert hh using 1
  ring

