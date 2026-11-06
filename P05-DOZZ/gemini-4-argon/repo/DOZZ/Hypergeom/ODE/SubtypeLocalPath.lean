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
theorem subtypeLocalSegmentValue_dist z w (t : unitInterval) :
    dist (subtypeLocalSegmentValue z w t) z = (t : ℝ) * dist w z := by
  calc
    dist (subtypeLocalSegmentValue z w t) z =
        ‖subtypeLocalSegmentValue z w t - z‖ := by rw [dist_eq_norm]
    _ = ‖(t : ℝ) • (w - z)‖ := by simp [subtypeLocalSegmentValue]
    _ = ‖(t : ℝ)‖ * ‖w - z‖ := norm_smul _ _
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

/-- Every point of a short subtype segment stays in the half-radius ball. -/
theorem subtypeLocalSegmentPath_mem_halfBall
    {U : Set ℂ} {z w : U} (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (z : ℂ) r ⊆ U)
    (hw : dist (z : ℂ) w < r / 2) (t : unitInterval) :
    dist ((subtypeLocalSegmentPath r hr hball hw t : U) : ℂ) (z : ℂ) < r / 2 := by
  change dist (subtypeLocalSegmentValue (z : ℂ) w t) (z : ℂ) < r / 2
  calc
    dist (subtypeLocalSegmentValue (z : ℂ) w t) (z : ℂ) =
        (t : ℝ) * dist (w : ℂ) (z : ℂ) :=
      subtypeLocalSegmentValue_dist (z : ℂ) w t
    _ ≤ dist (w : ℂ) (z : ℂ) := (by simpa using (mul_le_mul_of_nonneg_right t.property.2 (dist_nonneg : 0 ≤ dist (w : ℂ) (z : ℂ))))
    _ < r / 2 := by simpa [dist_comm] using hw

/-- The first half of a concatenated subtype path is its left path after linear
reparameterization. -/
theorem subtypePathFunction_trans_left
    {U : Set ℂ} {x y z : U} (p : Path x y) (q : Path y z)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    subtypePathFunction (p.trans q) (s / 2) = subtypePathFunction p s := by
  change ((p.trans q) (Set.projIcc 0 1 zero_le_one (s / 2)) : ℂ) =
    (p (Set.projIcc 0 1 zero_le_one s) : ℂ)
  rw [(Set.projIcc_of_mem zero_le_one (show s / 2 ∈ Icc (0 : ℝ) 1 by constructor <;> nlinarith [hs.1, hs.2])), (Set.projIcc_of_mem zero_le_one hs), Path.trans_apply]
  split_ifs with h
  · apply congrArg (fun t : unitInterval => (p t : ℂ))
    apply Subtype.ext
    change 2 * (s / 2) = s
    ring
  · exact (h (by change s / 2 ≤ 1 / 2; linarith [hs.2])).elim

/-- The second half of a concatenated subtype path is its right path after linear
reparameterization. -/
theorem subtypePathFunction_trans_right
    {U : Set ℂ} {x y z : U} (p : Path x y) (q : Path y z)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    subtypePathFunction (p.trans q) (1 / 2 + s / 2) = subtypePathFunction q s := by
  have ht : 1 / 2 + s / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> nlinarith [hs.1, hs.2]
  change ((p.trans q) (Set.projIcc 0 1 zero_le_one (1 / 2 + s / 2)) : ℂ) =
    (q (Set.projIcc 0 1 zero_le_one s) : ℂ)
  rw [(Set.projIcc_of_mem zero_le_one ht), (Set.projIcc_of_mem zero_le_one hs), Path.trans_apply]
  by_cases hs0 : s = 0
  · subst s
    simp [p.target, q.source]
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    split_ifs with h
    · exact ((show ¬ ((⟨1 / 2 + s / 2, ht⟩ : unitInterval) : ℝ) ≤ 1 / 2 by change ¬ (1 / 2 + s / 2 ≤ 1 / 2); linarith) h).elim
    · apply congrArg (fun t : unitInterval => (q t : ℂ))
      apply Subtype.ext
      change 2 * (1 / 2 + s / 2) - 1 = s
      ring

end DOZZ.Proofs
