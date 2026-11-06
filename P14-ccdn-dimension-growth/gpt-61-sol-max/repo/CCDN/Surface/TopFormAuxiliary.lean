/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.Surface.TopFormAuxiliaryEstimate
import CCDN.Surface.TopFormBadPrimes

/-! A coefficient-uniform auxiliary for an affine hypersurface with absolutely
irreducible leading form. This is the dimension-general form of CCDN (4-3-1). -/

@[expose] public section
namespace CCDN
open MvPolynomial

/-- The constant in the degree bound of the auxiliary polynomial for affine hypersurfaces in
`n + 2` variables with absolutely irreducible top-degree form, independent of the
coefficients. -/
noncomputable def topFormAuxiliaryConstant (n : ℕ)  :=
  affineHypersurfaceAuxiliaryConstant n *
    ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 2) + 2)

/-- The auxiliary constant `topFormAuxiliaryConstant n` is positive. -/
lemma topFormAuxiliaryConstant_pos (n : ℕ) : 0 < topFormAuxiliaryConstant n := by
  have hC := affineHypersurfaceAuxiliaryConstant_pos n
  have hH := zero_le_one.trans (hypersurfaceHeightConstant_one_le (n + 2))
  unfold topFormAuxiliaryConstant
  positivity

variable {n : ℕ} (f : CCDN.IntegerPolynomial (n + 2))

private theorem primitive_top_form_auxiliary  (hprim : PrimitiveIntegerPolynomial f)
    (hir : HasAbsIrreducibleTopForm f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      ↑g.totalDegree ≤ topFormAuxiliaryConstant n *
        ↑f.totalDegree ^ (4 - 1 / (n + 1 : ℝ)) *
          B ^ (1 / degreeRoot n f.totalDegree) := by
  have hfIr := hprim.irreducible_of_absolute_top hir
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f hir
  have hd := absolute_integer_polynomial_totalDegree_pos f habs
  let d := f.totalDegree
  let F := homogeneousComponent d f
  have hF0 := homogeneousComponent_totalDegree_ne_zero hfIr.ne_zero
  have hFd := (homogeneousComponent_isHomogeneous d f).totalDegree hF0
  let L := (integerCoefficientHeight F : ℝ)
  let q := heightExponent n d
  have hL := leading_height_one_le f hfIr.ne_zero
  have hratio := by
    calc
      _ ≤ hypersurfaceBadPrimeFactor F / L ^ q := div_le_div_of_nonneg_right
        (hypersurfaceBadPrimeFactor_le_top_homogeneousComponent f hir) (by positivity)
      _ ≤ _ := by
        simpa only [dimensionRoot, Nat.cast_add, Nat.cast_one] using
          hypersurface_badPrime_fractional_height_bound F hF0 hFd (r := n + 1) (by omega) hd
  obtain ⟨g, hg, hgdeg⟩ := affine_hypersurface_auxiliary f hprim hfIr hd hB
  refine ⟨g, hg, hgdeg.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left
    (affineAuxiliaryDegreeExpression_le_of_badPrime_ratio n hd hB hL hratio)
    (affineHypersurfaceAuxiliaryConstant_pos n).le
  unfold topFormAuxiliaryConstant
  convert hh using 1
  ring

/-- Uniform auxiliary existence for every integer equation whose highest
homogeneous component is absolutely irreducible. Integer content is removed
inside the proof; the final constant depends only on ambient dimension. -/
theorem top_form_auxiliary_rational 
    (hir : HasAbsIrreducibleTopForm f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : CCDN.IntegerPolynomial (n + 2),
      ¬ CCDN.rationalPolynomial f ∣ CCDN.rationalPolynomial g ∧
      ↑g.totalDegree ≤ topFormAuxiliaryConstant n *
        ↑f.totalDegree ^ (4 - 1 / (n + 1 : ℝ)) *
          B ^ (1 / degreeRoot n f.totalDegree) ∧
      ∀ x : IntPoint (n + 2), InBox x B → eval x f = 0 → eval x g = 0 := by
  have hf0 : f ≠ 0 := by intro hz; exact hir.ne_zero (by simp [hz])
  obtain ⟨c, u, hc, huprim, he⟩ := exists_primitive_integer_factor f hf0
  obtain ⟨huDegree, huTop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
  obtain ⟨g, ⟨hgnd, hgz⟩, hgdeg⟩ := primitive_top_form_auxiliary u huprim huTop hB
  have hudvd : u ∣ f := ⟨C c, by rw [he]; ring⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · intro h
    exact hgnd (huprim.rational_map_dvd_iff.mp ((map_dvd (CCDN.rationalPolynomial) hudvd).trans h))
  · simp_all
  · aesop

end CCDN
