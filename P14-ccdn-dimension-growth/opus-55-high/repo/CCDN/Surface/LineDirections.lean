/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.AffineLineLeading
import CCDN.Algebra.IdealZeroLocus
import CCDN.Height.ProjectiveZeroLocus
import CCDN.Hilbert.AffineCurveDegree
import CCDN.Plane.IntegralAffineLine
import CCDN.ForMathlib.MvPolynomial
import CCDN.Surface.TopFormIrreducibility

/-! Directions of rational affine lines on a surface. Lines with two
bounded integer points have a bounded projective direction and a spacing
bound expressed using its representative-independent projective height. -/

namespace CCDN
section
open MvPolynomial

/-- Evaluating the restriction `affineLinePolynomial a v f` of `f` to the line through `a` with
direction `v` at `t` gives the value of `f` at `a + t • v`. -/
lemma eval_affineLinePolynomial {K σ : Type*} [Field K]
    (a v : σ → K) (f : MvPolynomial σ K) (t : K) :
    (affineLinePolynomial a v f).eval t = eval (a + t • v) f := by
  have he : (Polynomial.evalRingHom t).comp (affineLinePolynomial a v) =
      eval (a + t • v) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [affineLinePolynomial]
    · intro i
      simp [affineLinePolynomial]
      ring
  exact RingHom.congr_fun he f

variable {n : ℕ}

theorem affineLinePolynomial_eq_zero_of_contained
    (a v : RatPoint n) (f : CoordinatePolynomial n)
    (hline : rationalAffineLine a v ⊆ zeroLocus f) :
    affineLinePolynomial a v f = 0 := by
  apply Polynomial.zero_of_eval_zero
  intro t
  rw [eval_affineLinePolynomial]
  exact hline ⟨t, rfl⟩

theorem rationalAffineLine_direction_top_zero
    (a v : RatPoint n) (f : MvPolynomial (Fin n) ℤ)
    (hline : rationalAffineLine a v ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) :
    eval v (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) = 0 := by
  have hpoly := affineLinePolynomial_eq_zero_of_contained a v _ hline
  have hc := affineLinePolynomial_top_coefficient a v (map (Int.castRingHom ℚ) f)
    f.totalDegree (totalDegree_map_le _ _)
  rw [hpoly, Polynomial.coeff_zero, ← map_homogeneousComponent] at hc
  exact hc.symm

/-- A line with more than one bounded integer point has a projective
direction on the leading form. Its integer point count is bounded using the
height of that projective point, independently of all chosen representatives. -/
theorem surface_line_projective_direction
    (f : MvPolynomial (Fin (n + 1)) ℤ) (L : Set (RatPoint (n + 1)))
    (hL : ∃ a v, L = rationalAffineLine a v)
    (hLf : L ⊆ zeroLocus (map (Int.castRingHom ℚ) f))
    {B : ℝ} (hB : 0 ≤ B) (hcount : 1 < count L B) :
    ∃ p : ProjectivePoint n,
      p ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
      0 < p.mulHeight ∧ p.mulHeight ≤ 2 * B ∧
      (∃ a, L = rationalAffineLine a p.rep) ∧
      (count L B : ℝ) ≤ 4 * B / p.mulHeight := by
  obtain ⟨a, v, rfl⟩ := hL
  obtain ⟨z, w, hw, hprim, hheight, hline, hcnt⟩ :=
    rationalAffineLine_integer_rep_and_count a v hB hcount
  let p := Projectivization.mk ℚ (rationalPoint w) (rationalPoint_ne_zero hw)
  have hpheight :=
    projective_direction_height w hw hprim
  have hp0 : 0 < p.mulHeight := by positivity
  have hzero := rationalAffineLine_direction_top_zero
    (rationalPoint z) (rationalPoint w) f (by grind)
  refine ⟨p, ?_, hp0, hpheight ▸ hheight, ?_, ?_⟩
  · exact (mem_projectiveZeroLocus_mk ((homogeneousComponent_isHomogeneous _ _).map _)
      (rationalPoint w) (rationalPoint_ne_zero hw)).mpr hzero
  · exact ⟨rationalPoint z, hline.trans
      (show rationalAffineLine _ _ = rationalAffineLine _ p.rep by
          have he := rfl.trans p.mk_rep.symm
          obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ p.rep (rationalPoint_ne_zero hw) p.rep_nonzero).mp he
          have heq := hc.symm
          rw [heq]
          exact rationalAffineLine_smul_direction _ p.rep c.ne_zero)⟩
  · rw [← hpheight] at hcnt
    have htwo : 1 ≤ 2 * B / p.mulHeight :=
      (le_div_iff₀ hp0).mpr (by grind)
    grind

