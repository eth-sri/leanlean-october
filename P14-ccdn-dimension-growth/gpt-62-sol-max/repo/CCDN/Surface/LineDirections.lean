/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

/-- Evaluating the restriction `affineLinePolynomial a v f` of `f` to the line through `a` with
direction `v` at `t` gives the value of `f` at `a + t • v`. -/
lemma eval_affineLinePolynomial {K σ : Type*} [Field K]
    (a v : σ → K) (f : MvPolynomial σ K) (t : K) :
    (affineLinePolynomial a v f).eval t = eval (a + t • v) f := by
  change Polynomial.evalRingHom t (affineLinePolynomial a v f) = _
  rw [affineLinePolynomial, map_eval₂Hom, eval]
  apply eval₂Hom_congr _ _ rfl
  · ext a
    simp
  · funext i
    simp; ring

private theorem affineLinePolynomial_eq_zero_of_contained {n : ℕ}
    (a v : RatPoint n) (f : CoordinatePolynomial n)
    (hline : rationalAffineLine a v ⊆ zeroLocus f) :
    affineLinePolynomial a v f = 0 := by
  apply Polynomial.zero_of_eval_zero
  intro t
  rw [eval_affineLinePolynomial]
  tauto

private theorem rationalAffineLine_direction_top_zero {n : ℕ}
    (a v : RatPoint n) (f : MvPolynomial (Fin n) ℤ)
    (hline : rationalAffineLine a v ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) :
    eval v (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) = 0 := by
  have hpoly := affineLinePolynomial_eq_zero_of_contained a v _ hline
  have hdegree : (map (Int.castRingHom ℚ) f).totalDegree ≤ f.totalDegree := totalDegree_map_le _ _
  have hc := affineLinePolynomial_top_coefficient a v (map (Int.castRingHom ℚ) f)
    f.totalDegree hdegree
  rw [hpoly, Polynomial.coeff_zero, ← map_homogeneousComponent] at hc
  exact hc.symm

/-- A line with more than one bounded integer point has a projective
direction on the leading form. Its integer point count is bounded using the
height of that projective point, independently of all chosen representatives. -/
theorem surface_line_projective_direction {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (L : Set (RatPoint (n + 1)))
    (hL : ∃ a v, L = rationalAffineLine a v)
    (hLf : L ⊆ zeroLocus (map (Int.castRingHom ℚ) f))
    {B : ℝ} (hcount : 1 < count L B) :
    ∃ p : ProjectivePoint n,
      p ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
      (∃ a, L = rationalAffineLine a p.rep) ∧
      (count L B : ℝ) ≤ 4 * B / p.mulHeight := by
  obtain ⟨a, v, rfl⟩ := hL
  obtain ⟨z, p, hheight, hline, hcnt⟩ := rationalAffineLine_integer_rep_and_count a v hcount
  have hzero := rationalAffineLine_direction_top_zero (rationalPoint z)
    (rationalPoint (primitiveProjectiveRep p)) f (hline ▸ hLf)
  refine ⟨p, ?_, ?_, ?_⟩
  · exact (mem_projectiveZeroLocus_primitive ((homogeneousComponent_isHomogeneous _ _).map _) p).mpr hzero
  · exact ⟨rationalPoint z, hline.trans (rationalAffineLine_eq_of_projective_eq _
      ((primitiveProjectiveRep_mk p).trans p.mk_rep.symm))⟩
  · have htwo : 1 ≤ 2 * B / p.mulHeight := (le_div_iff₀ p.mulHeight_pos).mpr (by simpa using hheight)
    simp only [mul_div_assoc] at hcnt htwo ⊢
    linarith

end
end CCDN
