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
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (f : X → ℂ) (hf : ContinuousOn f K)
    (U : Set ℂ) (hU : IsOpen U) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H U)
    (hpath : ∀ x ∈ K, f x ∈ U) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      ∀ x ∈ K,
        DifferentiableOn ℂ H (Metric.ball (f x) r) ∧
          ∀ z ∈ Metric.ball (f x) r, ‖H z‖ ≤ M := by
  let S := f '' K
  have hS : IsCompact S := by
    exact hK.image_of_continuousOn hf
  have hSU : S ⊆ U := by
    aesop
  obtain ⟨V, hSV, hVopen, hVbounded⟩ :=
    Metric.exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
      hS hU hSU hH.continuousOn
  let W := V ∩ U
  have hWopen := hVopen.inter hU
  have hSW : S ⊆ W := by tauto
  obtain ⟨δ, hδ, hδW⟩ := hS.exists_cthickening_subset_open hWopen hSW
  let r := δ / 2
  obtain ⟨B, hB⟩ := hVbounded.subset_closedBall (H 0)
  let M := max 0 (B + ‖H 0‖)
  refine ⟨r, M, by positivity, le_max_left .., ?_⟩
  intro x hx
  have hfxS : f x ∈ S := by tauto
  have hballW : Metric.ball (f x) r ⊆ W := by
    intro z hz
    apply hδW
    apply Metric.mem_cthickening_of_dist_le z (f x) δ S hfxS
    have hrδ : r ≤ δ := by grind
    exact (Metric.mem_ball.mp hz).le.trans hrδ
  have hballU : Metric.ball (f x) r ⊆ U := by aesop
  have hballV : Metric.ball (f x) r ⊆ V := by aesop
  refine ⟨hH.mono hballU, ?_⟩
  intro z hz
  have hnorm : ‖H z - H 0‖ ≤ B := by simpa [dist_eq_norm] using (hB ⟨z, hballV hz, rfl⟩)
  calc
    ‖H z‖ = ‖(H z - H 0) + H 0‖ := by simp
    _ ≤ ‖H z - H 0‖ + ‖H 0‖ := norm_add_le ..
    _ ≤ B + ‖H 0‖ := by linarith
    _ ≤ M := le_max_right ..

end DOZZ.Proofs
