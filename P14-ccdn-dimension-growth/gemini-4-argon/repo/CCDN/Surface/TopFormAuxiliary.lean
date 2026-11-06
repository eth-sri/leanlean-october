/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.Surface.TopFormAuxiliaryEstimate
import CCDN.Surface.TopFormBadPrimes

/-! A coefficient-uniform auxiliary for an affine hypersurface with absolutely
irreducible leading form. This is the dimension-general form of CCDN (4-3-1). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The constant in the degree bound of the auxiliary polynomial for affine hypersurfaces in
`n + 2` variables with absolutely irreducible top-degree form, independent of the
coefficients. -/
def topFormAuxiliaryConstant (n : ℕ) : ℝ :=
  affineHypersurfaceAuxiliaryConstant n *
    ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 2) + 2)

/-- The auxiliary constant `topFormAuxiliaryConstant n` is positive. -/
lemma topFormAuxiliaryConstant_pos (n : ℕ) : 0 < topFormAuxiliaryConstant n := by
  have hC := affineHypersurfaceAuxiliaryConstant_pos n
  have hH := zero_le_one.trans (hypersurfaceHeightConstant_one_le (n + 2))
  unfold topFormAuxiliaryConstant
  positivity

/-- Uniform auxiliary existence for every integer equation whose highest
homogeneous component is absolutely irreducible. Integer content is removed
inside the proof; the final constant depends only on ambient dimension. -/
theorem top_form_auxiliary_rational {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hir : HasAbsIrreducibleTopForm f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      (g.totalDegree : ℝ) ≤ topFormAuxiliaryConstant n *
        (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) *
          B ^ (1 / (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ))) ∧
      ∀ x : IntPoint (n + 2), InBox x B → eval x f = 0 → eval x g = 0 := by
  have hf0 : f ≠ 0 := fun hz => hir.ne_zero (by simp [hz])
  obtain ⟨c, u, hc, huprim, he⟩ := exists_primitive_integer_factor f hf0
  obtain ⟨huDegree, huTop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
  have huIr := huprim.irreducible_of_absolute_top huTop
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible u huTop
  have hd := absolute_integer_polynomial_totalDegree_pos u habs
  let d := u.totalDegree
  let F := homogeneousComponent d u
  have hF0 : F ≠ 0 := homogeneousComponent_totalDegree_ne_zero huIr.ne_zero
  have hFd : F.totalDegree = d := (homogeneousComponent_isHomogeneous d u).totalDegree hF0
  let L := (integerCoefficientHeight F : ℝ)
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let K := (n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 2)
  have hL : 1 ≤ L := leading_height_one_le u huIr.ne_zero
  have hratio : hypersurfaceBadPrimeFactor u / L ^ q ≤ K :=
    (div_le_div_of_nonneg_right
      (hypersurfaceBadPrimeFactor_le_top_homogeneousComponent u huTop) (by positivity)).trans
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        hypersurface_badPrime_fractional_height_bound F hF0 hFd (r := n + 1) (by omega) hd)
  obtain ⟨g, ⟨hg0, hgnd, hgz⟩, hgdeg⟩ := affine_hypersurface_auxiliary u huprim huIr hd hB
  have hudvd : u ∣ f := ⟨C c, by rw [he]; ring⟩
  refine ⟨g, hg0, fun h => hgnd (huprim.rational_map_dvd_iff.mp
    ((map_dvd (map (Int.castRingHom ℚ)) hudvd).trans h)), ?_, fun x hx hxf =>
      hgz x hx (by rw [he, eval_mul, eval_C] at hxf; exact (mul_eq_zero.mp hxf).resolve_left hc)⟩
  rw [← huDegree]
  refine hgdeg.trans ?_
  have hh := mul_le_mul_of_nonneg_left
    (affineAuxiliaryDegreeExpression_le_of_badPrime_ratio n hd hB hL hratio)
    (affineHypersurfaceAuxiliaryConstant_pos n).le
  unfold topFormAuxiliaryConstant
  convert hh using 1
  ring

end
end CCDN
