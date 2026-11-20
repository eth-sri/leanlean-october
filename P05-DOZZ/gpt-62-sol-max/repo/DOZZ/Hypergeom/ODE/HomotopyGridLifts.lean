/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.HomotopyGrid
public import DOZZ.Hypergeom.ODE.PathContinuation

/-! The finite homotopy grid supplies continuous Picard lifts on its lower and upper boundary
paths, with equal endpoint values. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- One horizontal Picard transfer in a finite homotopy grid. -/
noncomputable def homotopyGridRight
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (i j : ℕ) (v : E) : E :=
  if hi : i < G.N then
    if hj : j ≤ G.N then
      localPicardTransfer G.r G.M H (G.data i (Nat.le_of_lt hi) j hj) v (G.node (i + 1) j)
    else v
  else v

/-- The disk solution at one node of a horizontal row, initialized by the accumulated transfers
from the left boundary. -/
noncomputable def homotopyGridRowDisk
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (j : ℕ) (hj : j ≤ G.N)
    (i : ℕ) (hi : i ≤ G.N) : HolomorphicDiskSolution H G.r :=
  holomorphicDiskSolutionOfBound (G.node i j) G.r G.M H
    (G.data i hi j hj).differentiable
    (finiteGridHorizontal (homotopyGridRight G) 0 j i y)
    G.M_nonneg (G.data i hi j hj).bounded

/-- Extend the row-disk definition to all natural indices; only indices at most `N` are used. -/
noncomputable def homotopyGridRowChain
    {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (j : ℕ) (hj : j ≤ G.N)
    (i : ℕ) : HolomorphicDiskSolution H G.r :=
  homotopyGridRowDisk G j hj (min i G.N) (Nat.min_le_right _ _)

section
variable {Γ : ℝ × ℝ → ℂ} {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E} (G : HomotopyPicardGrid Γ U H y)
  (j : ℕ) (hj : j ≤ G.N) (i : ℕ)
include Γ U H y

theorem homotopyGridRowChain_center (hi : i ≤ G.N) :
    (homotopyGridRowChain G j hj i).center =
      Γ ((i : ℝ) / (G.N : ℝ), (j : ℝ) / (G.N : ℝ)) := by
  simp [homotopyGridRowChain, homotopyGridRowDisk, Nat.min_eq_left hi,
    holomorphicDiskSolutionOfBound, G.node_eq i hi j hj]

theorem homotopyGridRowChain_initial (hi : i ≤ G.N) :
    (homotopyGridRowChain G j hj i).initial =
      finiteGridHorizontal (homotopyGridRight G) 0 j i y := by
  simp [homotopyGridRowChain, homotopyGridRowDisk, Nat.min_eq_left hi,
    holomorphicDiskSolutionOfBound]

theorem homotopyGridRowChain_next_initial (hi : i < G.N) :
    (homotopyGridRowChain G j hj (i + 1)).initial =
      (homotopyGridRowChain G j hj i).solution (G.node (i + 1) j) := by
  have hi'  := Nat.le_of_lt hi
  simp [homotopyGridRowChain, homotopyGridRowDisk, Nat.min_eq_left hi',
    holomorphicDiskSolutionOfBound,
    finiteGridHorizontal, homotopyGridRight, localPicardTransfer, hi, hj]

end

section
variable {Γ : ℝ × ℝ → ℂ}

theorem homotopy_row_continuous (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : ContinuousOn (fun t => Γ (t, s)) (Icc (0 : ℝ) 1) :=
  hΓ.comp (by fun_prop) fun t ht => ⟨ht, hs⟩

/-- Each row of the grid gives a continuation lift whose endpoint is the horizontal transfer. -/
theorem exists_homotopyGrid_rowLift {U : Set ℂ} {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y)
    (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) (j : ℕ) (hj : j ≤ G.N) :
    ∃ L : PathContinuationLift (fun t => Γ (t, (j : ℝ) / (G.N : ℝ))) H y,
      L.value 1 = finiteGridHorizontal (homotopyGridRight G) 0 j G.N y := by
  let τ := fun i : ℕ => (i : ℝ) / (G.N : ℝ)
  let γ := fun t => Γ (t, τ j)
  let D := homotopyGridRowChain G j hj
  have hN : (0 : ℝ) < G.N := by exact_mod_cast G.N_pos
  have hτ : Monotone τ := fun i k h => div_le_div_of_nonneg_right (by exact_mod_cast h) hN.le
  have hc i (hi : i ≤ G.N) : (D i).center = γ (τ i) := homotopyGridRowChain_center G j hj i hi
  have hnode i (hi : i ≤ G.N) : (D i).center = G.node i j := (hc i hi).trans (G.node_eq i hi j hj).symm
  have hb i (hi : i ≤ G.N) (z) (hz : z ∈ Metric.ball (D i).center G.r) : ‖H z‖ ≤ G.M :=
    (G.data i hi j hj).bounded z (by simpa only [hnode i hi] using hz)
  have hinit : (D 0).initial = y := rfl
  have hcover : ∀ i < G.N, ∀ t ∈ Icc (τ i) (τ (i + 1)), γ t ∈ Metric.ball (D i).center (G.r / 2) := by
    intro i hi t ht
    rw [Metric.mem_ball, hc i hi.le]
    rcases hj.lt_or_eq with hlt | rfl
    · exact (G.cell_image i hi j hlt t ht (τ j) ⟨le_rfl, hτ (Nat.le_succ _)⟩).trans
        (by linarith [G.r_pos])
    · have hlast : G.N - 1 < G.N := by omega
      have hs : G.N - 1 + 1 = G.N := by omega
      have hmem : τ G.N ∈ Icc (τ (G.N - 1)) (τ (G.N - 1 + 1)) :=
        ⟨hτ (Nat.sub_le ..), hs ▸ le_rfl⟩
      have h₁ := G.cell_image i hi (G.N - 1) hlast t ht (τ G.N) hmem
      have h₂ := G.cell_image i hi (G.N - 1) hlast (τ i) ⟨le_rfl, hτ (Nat.le_succ _)⟩ (τ G.N) hmem
      have htri := dist_triangle (Γ (t, τ G.N)) (Γ (τ i, τ (G.N - 1))) (Γ (τ i, τ G.N))
      change dist (Γ (t, τ G.N)) (Γ (τ i, τ G.N)) < G.r / 2
      rw [dist_comm (Γ (τ i, τ (G.N - 1)))] at htri
      linarith
  have hover : ∀ i < G.N, ∀ z ∈ Metric.ball (D (i + 1)).center (G.r / 2),
      (D i).solution z = (D (i + 1)).solution z := by
    intro i hi z hz
    have hi₁ := Nat.succ_le_of_lt hi
    have hd := hcover i hi (τ (i + 1)) ⟨hτ (Nat.le_succ _), le_rfl⟩
    rw [← hc _ hi₁, Metric.mem_ball] at hd
    have hr : G.r / 2 < G.r := by linarith [G.r_pos]
    refine holomorphic_linear_system_solution_unique_of_eq_at _ _ _ H G.M_nonneg
      (fun w hw => hb _ hi₁ w (Metric.ball_subset_ball hr.le hw))
      (fun w hw => (D i).derivative w (Metric.ball_subset_ball' (by linarith) hw))
      (fun w hw => (D (i + 1)).derivative w (Metric.ball_subset_ball hr.le hw))
      (Metric.mem_ball_self (half_pos G.r_pos)) hz ?_
    rw [hnode _ hi₁, ← homotopyGridRowChain_next_initial G j hj i hi,
      ← hnode _ hi₁, (D (i + 1)).solution_center]
  obtain ⟨F, hF, hF₀, hF₁, hformula⟩ := exists_continuous_lift_from_disk_chain H
    (homotopy_row_continuous hΓ (pathContinuationMeshPoint_mem_unitInterval G.N_pos hj))
    G.N G.N_pos G.r G.r_pos D y (by simpa [τ] using hc 0 (Nat.zero_le _)) hinit hc hcover hover
  refine ⟨⟨G.N, G.N_pos, G.r, G.M, G.r_pos, G.M_nonneg, D, hinit, hc, hb, hcover, hover,
    F, hF, hF₀, hformula⟩, ?_⟩
  have hlast : (D G.N).center = γ 1 := by simpa [τ, div_self hN.ne'] using hc _ le_rfl
  exact (hF₁.trans ((congrArg (D G.N).solution hlast.symm).trans (D G.N).solution_center)).trans
    (homotopyGridRowChain_initial G j hj _ le_rfl)

end

end DOZZ.Proofs
