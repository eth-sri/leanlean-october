module

public import AnalyticESC.Basic

@[expose] public section

/-!
# The classes `S^ω_ε(I)` and `S^ω(I)`

The inclusion `f(cl B_ε) ⊆ B_ε` in condition (B) of the class `S^ω_ε(I)` follows from the other
conditions. Hence the classes `S^ω_ε(I)` decrease as `ε` increases, and their union `S^ω(I)` is
described by conditions on `[0,1]`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- Every point of `cl B_ε` lies within distance `ε` of a point of `I`. -/
theorem exists_mem_I_norm_sub_le {ε : ℝ} (hε : 0 ≤ ε) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    ∃ x ∈ I, ‖z - x‖ ≤ ε := by
  rw [closedNbhd, nbhd_eq_thickening] at hz
  have hz' := closure_thickening_subset_cthickening ε _ hz
  rw [isCompact_image_I.cthickening_eq_biUnion_closedBall hε] at hz'
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1 hz'
  exact ⟨x, hx, mem_closedBall_iff_norm.1 hzx⟩

/-- A map complex analytic on `B_{2ε}`, real at the real points of `B_{2ε}`, with
`f(I) ⊆ I` and `0 < |f'| < 1` on `cl B_ε`, lies in `S^ω_ε(I)`. -/
theorem _root_.Challenge.InClass.of_deriv {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (nbhd (2 * ε)))
    (him : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0)
    (hI : ∀ x ∈ I, (f x).re ∈ I)
    (hne : ∀ z ∈ closedNbhd ε, deriv f z ≠ 0)
    (hlt : ∀ z ∈ closedNbhd ε, ‖deriv f z‖ < 1) : InClass ε f := by
  refine ⟨hd, him, hI, ?_, hne, hlt⟩
  have hsub := closure_nbhd_subset_two hε
  obtain ⟨w, hw, hmax⟩ := (isCompact_closure_nbhd ε).exists_isMaxOn
    ⟨0, zero_mem_closure_nbhd hε⟩ (((hd.deriv (isOpen_nbhd _)).continuousOn.mono hsub).norm)
  intro z hz
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le hε.le hz
  have hmv := (convex_nbhd ε).closure.norm_image_sub_le_of_norm_deriv_le
    (fun y hy => hd.differentiableAt (nbhd_mem_nhds (hsub hy))) hmax (ofReal_mem_closure hε hx) hz
  refine ⟨(f x).re, hI x hx, ?_⟩
  rw [← Complex.ext (z := f x) (w := ((f x).re : ℂ)) rfl (him x (ofReal_mem_nbhd_two hε hx))]
  exact (hmv.trans (mul_le_mul_of_nonneg_left hzx (norm_nonneg _))).trans_lt
    (mul_lt_of_lt_one_left hε (hlt w hw))

end AnalyticESC
