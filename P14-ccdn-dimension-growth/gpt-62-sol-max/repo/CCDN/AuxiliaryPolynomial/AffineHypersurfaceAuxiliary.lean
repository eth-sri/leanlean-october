/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineAuxiliaryCases
import CCDN.AuxiliaryPolynomial.AffineAuxiliaryTranslationBound
import CCDN.AuxiliaryPolynomial.AffineBadPrimeTranslation
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.Height.ScaledHypersurfaceHeight

/-! The affine auxiliary theorem in every positive dimension and degree,
with the degree-loss-inclusive geometric bad-prime factor. This distinction
from the literal affine wording of CCDN Definition 3.2.1 is intentional. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The dimension constant multiplying `affineAuxiliaryDegreeExpression`. -/
def affineHypersurfaceAuxiliaryConstant (n : ℕ) : ℝ :=
  (2 * Real.exp ((n : ℝ) + 2)) * affineMinimumConstant n (affineAuxiliaryComparisonConstant n)

lemma affineHypersurfaceAuxiliaryConstant_pos (n : ℕ) :
    0 < affineHypersurfaceAuxiliaryConstant n := by
  have := zero_lt_one.trans_le (affineMinimumConstant_one_le n (affineAuxiliaryComparisonConstant n))
  unfold affineHypersurfaceAuxiliaryConstant
  positivity

/-- Every primitive irreducible integer affine hypersurface admits the
coefficient-sensitive auxiliary in the complete minimum form, using the
defined geometric bad-prime factor (which includes degree-dropping primes).
The constant depends only on the dimension. -/
theorem affine_hypersurface_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineHypersurfaceAuxiliaryConstant n *
        affineAuxiliaryDegreeExpression n f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (hypersurfaceBadPrimeFactor f) := by
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := hypersurfaceBadPrimeFactor f
  let A := affineAuxiliaryComparisonConstant n
  have hL : 1 ≤ L := leading_height_one_le f hir.ne_zero
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg f
  obtain ⟨a, ha, hc⟩ := exists_bounded_affine_translation_nonzero_constant f hir.ne_zero
  let t := affineTranslation ℤ a f
  have htprim : PrimitiveIntegerPolynomial t := hprim.translate_affine a
  have htir : Irreducible t := (affineTranslation_irreducible_iff a f).mpr hir
  have htd : t.totalDegree = d := affineTranslation_totalDegree a f
  have htdpos : 0 < t.totalDegree := htd ▸ hd
  have hB' : 1 ≤ B + d := by linarith
  obtain ⟨g, hg, hgdeg⟩ :=
    affine_auxiliary_minimum_nonzero_constant t htprim htir htdpos hc hB'
  have habox (j) : |(a j : ℝ)| ≤ d := by
    have h0 : (0 : ℝ) ≤ a j := by exact_mod_cast (ha j).1
    rw [abs_of_nonneg h0]
    exact_mod_cast (ha j).2
  obtain ⟨G, hG, hGdeg⟩ := affine_auxiliary_translation_transport f g a hg habox
  refine ⟨G, hG, ?_⟩
  have htle : (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n d A (B + d) L b := by
    have htop : homogeneousComponent t.totalDegree t = homogeneousComponent d f :=
      affineTranslation_leading_homogeneousComponent a f
    rw [htop, htd] at hgdeg
    simpa [t, hypersurfaceBadPrimeFactor_affineTranslation] using hgdeg
  rw [hGdeg]
  apply htle.trans
  have hh := mul_le_mul_of_nonneg_left (affineAuxiliaryDegreeExpression_translation (n := n) hd hB hL hb)
    ((affineMinimumConstant_one_le n A).trans' zero_le_one)
  simpa only [affineMinimumAuxiliaryBound, affineHypersurfaceAuxiliaryConstant, A,
    mul_left_comm, mul_assoc] using hh

end
end CCDN
