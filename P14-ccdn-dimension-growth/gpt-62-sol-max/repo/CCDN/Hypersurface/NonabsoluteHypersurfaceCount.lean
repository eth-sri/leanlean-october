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
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import CCDN.Algebra.HomogeneousLinearDescent

/-! Dimension growth for non-geometrically-irreducible rational
hypersurfaces in every ambient dimension. The dependence on the degree
is quadratic; the explicit constant depends only on dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A set whose bounded integer points lie in a proper intersection of two hypersurfaces
has the corresponding codimension-two grid bound. -/
theorem proper_intersection_count_le {n : ℕ}
    (f g : CoordinatePolynomial (n + 2)) (hf : Prime f) (hfg : ¬ f ∣ g)
    (hgd : g.totalDegree ≤ f.totalDegree) {B : ℝ} (hB : 1 ≤ B)
    {X : Set (RatPoint (n + 2))}
    (hX : ∀ x : IntPoint (n + 2), InBox x B → rationalPoint x ∈ X →
      rationalPoint x ∈ zeroLocus f ∩ zeroLocus g) :
    (count X B : ℝ) ≤ (3 * (n + 2) : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * B ^ n := by
  classical
  let T := integralPoints X B
  let d := f.totalDegree
  let S := (integerInterval B).image (fun t : ℤ => (t : ℚ))
  let z : T → Fin (n + 2) → ℚ := fun x => rationalPoint x.val
  have hz : Function.Injective z := (rationalPoint_injective _).comp Subtype.val_injective
  have hzS (x : T) (j : Fin (n + 2)) : z x j ∈ S :=
    Finset.mem_image.mpr ⟨x.val j,
      mem_integerInterval.mpr ((mem_integralPoints.mp x.property).1 j), rfl⟩
  have hzfg (x : T) := hX x.val (mem_integralPoints.mp x.property).1 (mem_integralPoints.mp x.property).2
  have hgrid := proper_intersection_grid_card_le f g hf hfg le_rfl hgd S z hz hzS
    (fun x => (hzfg x).1) (fun x => (hzfg x).2)
  have hcard : (count X B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (d : ℝ) ^ 2 * (S.card : ℝ) ^ n := by
    exact_mod_cast (show T.card ≤ (n + 2) ^ n * d ^ 2 * S.card ^ n by
      simpa only [Fintype.card_coe] using hgrid)
  have hScard : (S.card : ℝ) ≤ 3 * B := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ Int.cast_injective]
    linarith [integerInterval_card_le (zero_le_one.trans hB)]
  calc
    _ ≤ ((n + 2 : ℝ) ^ n * (d : ℝ) ^ 2) * (S.card : ℝ) ^ n := hcard
    _ ≤ ((n + 2 : ℝ) ^ n * (d : ℝ) ^ 2) * (3 * B) ^ n := by gcongr
    _ = _ := by rw [mul_pow, mul_pow]; ring

section

variable {K : Type*}
  [Field K] [Algebra ℚ K] {n : ℕ}
  (f : CoordinatePolynomial (n + 2)) (hir : Irreducible f)
  (hred : ¬ Irreducible (map (algebraMap ℚ K) f))
  {B : ℝ}
include K n f hir hred B

/-- An irreducible rational polynomial `f` in `n + 2` variables that becomes reducible over some
extension field has at most `(3 * (n + 2)) ^ n * deg f ^ 2 * B ^ n` integral zeros of height
at most `B`, for every `B ≥ 1`. -/
theorem nonabsolute_hypersurface_dimension_growth (hB : 1 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤
      (3 * (n + 2) : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * B ^ n := by
  obtain ⟨g, _, hgd, hfg, _, hzero⟩ := nonabsolute_auxiliary f hir hred
  exact proper_intersection_count_le f g hir.prime hfg hgd hB (fun _ _ h => ⟨h, hzero _ h⟩)

end
end
end CCDN
