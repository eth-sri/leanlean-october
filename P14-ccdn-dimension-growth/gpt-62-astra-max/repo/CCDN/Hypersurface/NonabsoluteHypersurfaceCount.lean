/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Hilbert.CompleteIntersectionGridBound
import CCDN.Hypersurface.NonabsoluteSurfaceCount

/-! Dimension growth for non-geometrically-irreducible rational
hypersurfaces in every ambient dimension. The dependence on the degree
is quadratic; the explicit constant depends only on dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K : Type*} [Field K] [Algebra ℚ K] {n d : ℕ} (f : CoordinatePolynomial (n + 2))
    (hir : Irreducible f) (hred : ¬ Irreducible (map (algebraMap ℚ K) f)) {B : ℝ}

/-- If `f` is a prime rational polynomial in `n + 2` variables not dividing `g`, and both have
total degree at most `d`, then the common zero set of `f` and `g` has at most
`(n + 2) ^ n * d ^ 2 * (2 * B + 1) ^ n` integral points of height at most `B`. -/
theorem proper_intersection_count_le_box (g : CoordinatePolynomial (n + 2)) (hf : Prime f) (hfg : ¬ f ∣ g)
    (hfd : f.totalDegree ≤ d) (hgd : g.totalDegree ≤ d)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus f ∩ zeroLocus g) B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (d : ℝ) ^ 2 * (2 * B + 1) ^ n := by
  classical
  let T := integralPoints (zeroLocus f ∩ zeroLocus g) B
  let S := (Finset.Icc (-⌊B⌋) ⌊B⌋).image (fun t : ℤ => (t : ℚ))
  let z : T → Fin (n + 2) → ℚ := fun x => rationalPoint x.val
  have hz := (rationalPoint_injective _).comp (Subtype.val_injective (p:=(· ∈ T)))
  have hzS (x : T) (j : Fin (n + 2)) : z x j ∈ S :=
    Finset.mem_image.mpr ⟨_,mem_boxInterval.mpr ((mem_integralPoints.mp x.2).1 j),rfl⟩
  have hzfg (x : T)  :=
    (mem_integralPoints.mp x.property).2
  have hgrid := proper_intersection_grid_card_le f g hf hfg hfd hgd S z hz hzS
    (fun x => (hzfg x).1) (fun x => (hzfg x).2)
  have hcard : (count (zeroLocus f ∩ zeroLocus g) B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (d : ℝ) ^ 2 * (S.card : ℝ) ^ n := by
    exact_mod_cast (show T.card ≤ (n + 2) ^ n * d ^ 2 * S.card ^ n by
      grind [Fintype.card_coe])
  have hScard : (S.card : ℝ) ≤ 2 * B + 1 := by
    simpa [S,boxInterval,Finset.card_image_of_injective _ Int.cast_injective] using boxInterval_card hB
  exact hcard.trans (by gcongr)

include hir hred in
/-- Rationally irreducible full equations which split over an
extension satisfy affine dimension growth with quadratic degree
dependence. The dimension-only factor here is not asserted to be the
sharp constant one in CCDN Corollary 4.1.4. -/
private theorem nonabsolute_hypersurface_count_le (hB : 0 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) ^ n := by
  obtain ⟨g, _, hgd, hfg, hzero⟩ := nonabsolute_affine_auxiliary f hir hred
  have hsubset : zeroLocus f ⊆ zeroLocus f ∩ zeroLocus g :=
    by aesop
  have hcount : (count (zeroLocus f) B : ℝ) ≤
      (count (zeroLocus f ∩ zeroLocus g) B : ℝ) := by
    exact_mod_cast count_mono hsubset (le_refl B)
  exact hcount.trans (proper_intersection_count_le_box f g hir.prime hfg le_rfl hgd hB)

include hir hred in
/-- An irreducible rational polynomial `f` in `n + 2` variables that becomes reducible over some
extension field has at most `(3 * (n + 2)) ^ n * deg f ^ 2 * B ^ n` integral zeros of height
at most `B`, for every `B ≥ 1`. -/
theorem nonabsolute_hypersurface_dimension_growth (hB : 1 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤
      (3 * (n + 2) : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * B ^ n := by
  calc
    _ ≤ (n + 2) ^ n * f.totalDegree ^ 2 * (2 * B + 1) ^ n := (nonabsolute_hypersurface_count_le f hir hred (show 0 ≤ B by linarith))
    _ ≤ (n + 2) ^ n * f.totalDegree ^ 2 * (3 * B) ^ n := by
      gcongr
      linarith
    _ = _ := by grind [mul_pow]

end
end CCDN
