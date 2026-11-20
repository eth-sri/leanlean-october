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
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.Surface.TopFormBadPrimes

/-! A coefficient-uniform auxiliary for an affine hypersurface with absolutely
irreducible leading form. This is the dimension-general form of CCDN (4-3-1). -/

@[expose] public section
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
    ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 2) + 1)

/-- The auxiliary constant `topFormAuxiliaryConstant n` is positive. -/
lemma topFormAuxiliaryConstant_pos : 0 < topFormAuxiliaryConstant n := by
  have hC := affineHypersurfaceAuxiliaryConstant_pos n
  have hH := zero_le_one.trans (hypersurfaceHeightConstant_one_le (n + 2))
  unfold topFormAuxiliaryConstant
  positivity

end

variable {n : ℕ} (f : IntegerPolynomial (n + 2))

private theorem primitive_top_form_auxiliary (hprim : PrimitiveIntegerPolynomial f)
    (hir : HasAbsIrreducibleTopForm f)
    {B : ℝ} (hB : 1 ≤ B) :
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
  let L := (integerCoefficientHeight F)
  let q := 1 / ((n + 1 : ℝ) * d * d ^ (1 / (n + 1 : ℝ)))
  have hL := leading_height_one_le f hfIr.ne_zero
  have hratio : hypersurfaceBadPrimeFactor f / (L : ℝ)^q ≤ (n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 2) := by
    calc
      _ ≤ hypersurfaceBadPrimeFactor F / L ^ q := div_le_div_of_nonneg_right
        (hypersurfaceBadPrimeFactor_le_top_homogeneousComponent f hir) (by positivity)
      _ ≤ _ := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hypersurface_badPrime_fractional_height_bound F hF0 hFd (r := n + 1) (by omega) hd
  exact affine_hypersurface_auxiliary f hprim habs hd hB ((min_le_left _ _).trans hratio)

/-- Uniform auxiliary existence for every integer equation whose highest
homogeneous component is absolutely irreducible. Integer content is removed
inside the proof; the final constant depends only on ambient dimension. -/
theorem top_form_auxiliary_rational
    (hir : HasAbsIrreducibleTopForm f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : IntegerPolynomial (n + 2), g ≠ 0 ∧
      ¬ rationalEquation f ∣ rationalEquation g ∧
      (g.totalDegree : ℝ) ≤ topFormAuxiliaryConstant n *
        (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) *
          B ^ (1 / (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ))) ∧
      ∀ x : IntPoint (n + 2), InBox x B → eval x f = 0 → eval x g = 0 := by
  have hf0 : f ≠ 0 := by intro hz; exact hir.ne_zero (by simp [hz])
  obtain ⟨c, u, hc, huprim, he⟩ := exists_primitive_integer_factor f hf0
  obtain ⟨huDegree, huTop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
  obtain ⟨g, ⟨hg0, hgnd, hgz⟩, hgdeg⟩ := primitive_top_form_auxiliary u huprim huTop hB
  have hudvd : u ∣ f := ⟨C c, by rw [he]; ring⟩
  refine ⟨g, hg0, ?_, ?_, ?_⟩
  · intro h
    exact hgnd (huprim.rational_map_dvd_iff.mp ((map_dvd (rationalEquation) hudvd).trans h))
  grind
  · intro x hx hxf
    apply hgz x hx
    aesop

end
end CCDN
