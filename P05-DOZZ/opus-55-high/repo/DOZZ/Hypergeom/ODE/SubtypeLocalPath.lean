/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlanePathIndependence

/-! Local straight paths and concatenation identities for paths in subtypes of ℂ. -/

@[expose] public section

open Set unitInterval

namespace DOZZ.Proofs

/-- The affine segment from `z` to `w`, parameterized by the unit interval. -/
noncomputable def subtypeLocalSegmentValue (z w : ℂ) (t : unitInterval) : ℂ :=
  z + (t : ℝ) • (w - z)

/-- Distance from a point on the affine segment to its initial endpoint. -/
theorem subtypeLocalSegmentValue_dist (z w : ℂ) (t : unitInterval) :
    dist (subtypeLocalSegmentValue z w t) z = (t : ℝ) * dist w z := by
  calc
    dist _ z =
        ‖subtypeLocalSegmentValue z w t - z‖ := by rw [dist_eq_norm]
    _ = ‖(t : ℝ) • (w - z)‖ := by simp [subtypeLocalSegmentValue]
    _ = ‖(t : ℝ)‖ * ‖w - z‖ := norm_smul ..
    _ = (t : ℝ) * dist w z := by
      rw [Real.norm_eq_abs, abs_of_nonneg t.property.1, dist_eq_norm]

/-- A short segment lies inside the supplied open subtype disk. -/
noncomputable def subtypeLocalSegmentPath
    {U : Set ℂ} {z w : U} (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (z : ℂ) r ⊆ U)
    (hw : dist (z : ℂ) w < r / 2) : Path z w := by
  let g : unitInterval → ℂ := subtypeLocalSegmentValue (z : ℂ) w
  have hg : Continuous g := by fun_prop [subtypeLocalSegmentValue]
  have hgmem (t : unitInterval) : g t ∈ U := by
    have hmul : (t : ℝ) * dist (w : ℂ) (z : ℂ) ≤ dist (w : ℂ) (z : ℂ) := by
      have h := mul_le_mul_of_nonneg_right t.property.2
        (dist_nonneg : 0 ≤ dist (w : ℂ) (z : ℂ))
      simpa using h
    have hdist : dist (g t) (z : ℂ) < r / 2 := by
      calc
        dist (g t) (z : ℂ) = (t : ℝ) * dist (w : ℂ) (z : ℂ) :=
          subtypeLocalSegmentValue_dist (z : ℂ) w t
        _ ≤ dist (w : ℂ) (z : ℂ) := hmul
        _ < r / 2 := by simpa [dist_comm] using hw
    apply hball (Metric.ball_subset_ball (by linarith) (Metric.mem_ball.mpr hdist))
  let f : C(unitInterval, U) :=
    ⟨fun t => ⟨g t, hgmem t⟩, hg.subtype_mk hgmem⟩
  refine ⟨f, ?_, ?_⟩
  · apply Subtype.ext
    simp [f, g, subtypeLocalSegmentValue]
  · apply Subtype.ext
    simp [f, g, subtypeLocalSegmentValue]
section
variable {U : Set ℂ}

/-- Every point of a short subtype segment stays in the half-radius ball. -/
theorem subtypeLocalSegmentPath_mem_halfBall
    {z w : U} (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (z : ℂ) r ⊆ U)
    (hw : dist (z : ℂ) w < r / 2) (t : unitInterval) :
    dist ((subtypeLocalSegmentPath r hr hball hw t : U) : ℂ) (z : ℂ) < r / 2 := by
  change dist (subtypeLocalSegmentValue (z : ℂ) w t) (z : ℂ) < r / 2
  have hmul : (t : ℝ) * dist (w : ℂ) (z : ℂ) ≤ dist (w : ℂ) (z : ℂ) := by
    have h := mul_le_mul_of_nonneg_right t.property.2
      (dist_nonneg : 0 ≤ dist (w : ℂ) (z : ℂ))
    linarith
  calc
    dist (subtypeLocalSegmentValue (z : ℂ) w t) (z : ℂ) =
        (t : ℝ) * dist (w : ℂ) (z : ℂ) :=
      subtypeLocalSegmentValue_dist (z : ℂ) w t
    _ ≤ dist (w : ℂ) (z : ℂ) := hmul
    _ < r / 2 := by simpa [dist_comm] using hw
section
variable {x y z : U} (p : Path x y) (q : Path y z) {s : ℝ}
section
variable (hs : s ∈ Icc (0 : ℝ) 1)
include hs

/-- The first half of a concatenated subtype path is its left path after linear
reparameterization. -/
theorem subtypePathFunction_trans_left
    :
    subtypePathFunction (p.trans q) (s / 2) = subtypePathFunction p s := by
  have hs2 : s / 2 ∈ Icc (0 : ℝ) 1 := by grind
  have hproj2 := Set.projIcc_of_mem zero_le_one hs2
  have hproj := Set.projIcc_of_mem zero_le_one hs
  change ((p.trans q) _ : ℂ) =
    (p _ : ℂ)
  grind

/-- The second half of a concatenated subtype path is its right path after linear
reparameterization. -/
theorem subtypePathFunction_trans_right
    :
    subtypePathFunction (p.trans q) (1 / 2 + s / 2) = subtypePathFunction q s := by
  have ht : 1 / 2 + s / 2 ∈ Icc (0 : ℝ) 1 := by grind
  change ((p.trans q) _ : ℂ) =
    (q _ : ℂ)
  rw [(Set.projIcc_of_mem zero_le_one ht), (Set.projIcc_of_mem zero_le_one hs), Path.trans_apply]
  by_cases hs0 : s = 0
  · simp_all
  grind

end

end

end

end DOZZ.Proofs
