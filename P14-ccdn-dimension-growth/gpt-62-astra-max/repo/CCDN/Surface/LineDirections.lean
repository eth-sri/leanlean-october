/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.AffineLineLeading
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Plane.IntegralAffineLine
import CCDN.ForMathlib.MvPolynomial
import CCDN.Surface.TopFormIrreducibility

/-! Directions of rational affine lines on a surface. Lines with two
bounded integer points have a bounded projective direction and a spacing
bound expressed using its representative-independent projective height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

open Finset

/-- Attach the projective direction to each line contributing multiple points. -/
theorem line_direction_bound {n : ℕ} (f : IntegerPolynomial (n+1)) (L : Set (RatPoint (n+1)))
    (hL : ∃ a v, L = rationalAffineLine a v) (hf : L ⊆ zeroLocus (rationalEquation f))
    {B : ℝ} (hB : 0 ≤ B) (hcount : 1 < count L B) : ∃ p : ProjectivePoint n,
    p ∈ projectiveZeroLocus (rationalEquation (homogeneousComponent f.totalDegree f)) ∧
    (∃ a, L = rationalAffineLine a p.rep) ∧ (count L B:ℝ) ≤ 8*B/p.mulHeight := by
  obtain ⟨a,v,rfl⟩ := hL
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp hcount
  obtain ⟨hxB,t,ht⟩ := mem_integralPoints.mp hx
  have hv : v ≠ 0 := by
    rintro rfl; obtain ⟨s,hs⟩ := (mem_integralPoints.mp hy).2
    apply ne ((rationalPoint_injective _) ?_); simpa using ht.trans (by simpa using hs.symm)
  let p := Projectivization.mk ℚ v hv
  have he : rationalAffineLine a v = rationalAffineLine (rationalPoint x) p.rep := by rw [ht,← line_eq_rep _ _ hv _ rfl,rationalAffineLine_shift_base]
  have hc := primitive_line_spacing p x hB hxB
  rw [← he] at hc
  refine ⟨p,?_,⟨_,he⟩,?_⟩
  · apply (mem_projectiveZeroLocus_mk ((homogeneousComponent_isHomogeneous _ _).map _) _ hv).mpr
    have hz : affineLinePolynomial a v (rationalEquation f) = 0 := Polynomial.zero_of_eval_zero _ fun r => by
      rw [eval_affineLinePolynomial]; exact hf ⟨r,rfl⟩
    have hh := affineLinePolynomial_top_coefficient a v (rationalEquation f) _ (totalDegree_map_le _ _)
    rw [← map_homogeneousComponent] at hh
    simpa [hz] using hh.symm
  · have ht : (2:ℝ) ≤ count (rationalAffineLine a v) B := by exact_mod_cast hcount
    calc _ ≤ 2*(4*B/p.mulHeight) := by linarith only [hc,ht]
         _ = _ := by ring

end
end CCDN
