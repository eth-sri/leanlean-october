/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.Bounded
public import DOZZ.Hypergeom.ODE.LocalTransfer

/-! Compact subsets of an open regular domain admit a uniform family of coefficient disks and a
uniform coefficient norm bound. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_uniform_holomorphic_disks_on_compact
    {X : Type*} [TopologicalSpace X] {K}
    (hK : IsCompact K) (f : X → ℂ) (hf : ContinuousOn f K)
    U (hU : IsOpen U) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H U)
    (hpath : ∀ x ∈ K, f x ∈ U) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      ∀ x ∈ K,
        DifferentiableOn ℂ H (Metric.ball (f x) r) ∧
          ∀ z ∈ Metric.ball (f x) r, ‖H z‖ ≤ M := by
  let S := f '' K
  have hS : IsCompact S := by
    dsimp [S]
    exact hK.image_of_continuousOn hf
  have hSU : S ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact hpath x hx
  obtain ⟨V, hSV, hVopen, hVbounded⟩ :=
    Metric.exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
      hS hU hSU hH.continuousOn
  obtain ⟨δ, hδ, hδW⟩ := hS.exists_cthickening_subset_open (hVopen.inter hU) (fun z hz => ⟨hSV hz, hSU hz⟩)
  let r := δ / 2
  obtain ⟨B, hB⟩ := hVbounded.subset_closedBall (H 0)
  let M := max 0 (B + ‖H 0‖)
  refine ⟨r, M, by dsimp [r]; linarith, le_max_left _ _, ?_⟩
  intro x hx
  have hballW : Metric.ball (f x) r ⊆ (V ∩ U) := by
    intro z hz
    apply hδW
    apply Metric.mem_cthickening_of_dist_le z (f x) δ S ⟨x, hx, rfl⟩
    exact (Metric.mem_ball.mp hz).le.trans (by dsimp [r]; linarith)
  have hballV : Metric.ball (f x) r ⊆ V := fun _ hz => (hballW hz).1
  refine ⟨hH.mono (fun _ hz => (hballW hz).2), ?_⟩
  intro z hz
  have : ‖H z - H 0‖ ≤ B := by simpa [dist_eq_norm] using (hB ⟨z, hballV hz, rfl⟩)
  calc
    ‖H z‖ = ‖(H z - H 0) + H 0‖ := by congr 1; abel
    _ ≤ ‖H z - H 0‖ + ‖H 0‖ := norm_add_le _ _
    _ ≤ B + ‖H 0‖ := by linarith
    _ ≤ M := le_max_right _ _

end DOZZ.Proofs
