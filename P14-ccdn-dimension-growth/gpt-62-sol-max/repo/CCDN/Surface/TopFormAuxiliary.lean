/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ScaledHypersurfaceHeight
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
    (badPrimeHeightConstant n (n + 1) + 2)

/-- The auxiliary constant `topFormAuxiliaryConstant n` is positive. -/
lemma topFormAuxiliaryConstant_pos (n : ℕ) : 0 < topFormAuxiliaryConstant n := by
  have hC := affineHypersurfaceAuxiliaryConstant_pos n
  have hH := badPrimeHeightConstant_nonneg n (n + 1)
  unfold topFormAuxiliaryConstant
  positivity

section

variable {n : ℕ}
  (f : MvPolynomial (Fin (n + 2)) ℤ)
include n f

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
  have hF0 : F ≠ 0 := homogeneousComponent_totalDegree_ne_zero hfIr.ne_zero
  have hFd : F.totalDegree = d := (homogeneousComponent_isHomogeneous d f).totalDegree hF0
  let L := (integerCoefficientHeight F : ℝ)
  let q := heightExponent n d
  let K := badPrimeHeightConstant n (n + 1)
  have hL : 1 ≤ L := leading_height_one_le f hfIr.ne_zero
  have hratio : hypersurfaceBadPrimeFactor f / L ^ q ≤ K := by
    calc
      _ ≤ hypersurfaceBadPrimeFactor F / L ^ q := div_le_div_of_nonneg_right
        (hypersurfaceBadPrimeFactor_le_top_homogeneousComponent f hir) (by positivity)
      _ ≤ _ := by
        simpa [L, q, K] using hypersurface_badPrime_height_transfer (n := n) F hFd hd le_rfl hL
  obtain ⟨g, hg, hgdeg⟩ := affine_hypersurface_auxiliary f hprim hfIr hd hB
  refine ⟨g, hg, hgdeg.trans ?_⟩
  unfold affineAuxiliaryDegreeExpression topFormAuxiliaryConstant
  calc
    _ ≤ affineHypersurfaceAuxiliaryConstant n *
        ((d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * B ^ (1 / degreeRoot n d) * (K + 2)) := by
      have := (affineHypersurfaceAuxiliaryConstant_pos n).le
      gcongr
      exact (min_le_right _ _).trans hratio
    _ = _ := by dsimp only [K, d, degreeRoot]; ring

/-- Uniform auxiliary existence for every integer equation whose highest
homogeneous component is absolutely irreducible. Integer content is removed
inside the proof; the final constant depends only on ambient dimension. -/
theorem top_form_auxiliary_rational
    (hir : HasAbsIrreducibleTopForm f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      (g.totalDegree : ℝ) ≤ topFormAuxiliaryConstant n *
        (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) *
          B ^ (1 / (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ))) ∧
      ∀ x : IntPoint (n + 2), InBox x B → eval x f = 0 → eval x g = 0 := by
  obtain ⟨u, hprim, hd, hutop, ha⟩ := exists_primitive_top_form hir
  obtain ⟨g, ⟨hg, hnd, hz⟩, hdeg⟩ := primitive_top_form_auxiliary u hprim hutop hB
  refine ⟨g, hg, fun h => hnd (hprim.rational_map_dvd_iff.mp (ha.dvd'.trans h)), hd ▸ hdeg, ?_⟩
  intro x hx hxf
  apply hz x hx
  rw [← eval_rationalPoint_map_eq_zero, rational_model_zero_iff ha, eval_rationalPoint_map_eq_zero]
  exact hxf

end

end
end CCDN
