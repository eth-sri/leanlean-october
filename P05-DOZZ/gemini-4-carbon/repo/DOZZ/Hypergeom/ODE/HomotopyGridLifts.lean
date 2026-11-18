/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.HomotopyGrid
public import DOZZ.Hypergeom.ODE.PathLift

/-! The finite homotopy grid supplies continuous Picard lifts on its lower and upper boundary
paths, with equal endpoint values. -/

@[expose] public section

noncomputable section
open Set

namespace DOZZ.Proofs

variable {Γ : ℝ × ℝ → ℂ} {U : Set ℂ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- One horizontal Picard transfer in a finite homotopy grid. -/
def homotopyGridRight {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (i j : ℕ) (v : E) : E :=
  if hi : i < G.N then
    if hj : j ≤ G.N then
      localPicardTransfer G.r G.M H (G.data i (Nat.le_of_lt hi) j hj) v (G.node (i + 1) j)
    else v
  else v

/-- The disk solution at one node of a horizontal row, initialized by the accumulated transfers
from the left boundary. -/
def homotopyGridRowDisk {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (j : ℕ) (hj : j ≤ G.N)
    (i : ℕ) (hi : i ≤ G.N) : HolomorphicDiskSolution H G.r :=
  holomorphicDiskSolutionOfBound (G.node i j) G.r G.M H
    (G.data i hi j hj).differentiable
    (finiteGridHorizontal (homotopyGridRight G) 0 j i y)
    G.M_nonneg (G.data i hi j hj).bounded

/-- Extend the row-disk definition to all natural indices; only indices at most `N` are used. -/
def homotopyGridRowChain {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y) (j : ℕ) (hj : j ≤ G.N)
    (i : ℕ) : HolomorphicDiskSolution H G.r :=
  homotopyGridRowDisk G j hj (min i G.N) (Nat.min_le_right _ _)

/-- A finite homotopy grid yields continuous local-solution lifts of both boundary paths, and
their terminal values agree. The local formulas are retained for later lift-uniqueness arguments. -/
theorem homotopy_grid_boundary_lifts_endpoint_eq_with_formulas
    {H : ℂ → E →L[ℂ] E} {y : E}
    (G : HomotopyPicardGrid Γ U H y)
    (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :
    ∃ bottom top : ℝ → E,
      ContinuousOn bottom (Icc (0 : ℝ) 1) ∧
      ContinuousOn top (Icc (0 : ℝ) 1) ∧
      bottom 0 = y ∧ top 0 = y ∧ bottom 1 = top 1 ∧
      (∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
        (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
        bottom t = (homotopyGridRowChain G 0 (by omega) i).solution (Γ (t, 0))) ∧
      (∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
        (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
        top t = (homotopyGridRowChain G G.N le_rfl i).solution (Γ (t, 1))) ∧
      (∀ i ≤ G.N, (homotopyGridRowChain G 0 (by omega) i).center =
        Γ ((i : ℝ) / (G.N : ℝ), 0)) ∧
      (∀ i ≤ G.N, ∀ z ∈ Metric.ball
        (homotopyGridRowChain G 0 (by omega) i).center G.r, ‖H z‖ ≤ G.M) ∧
      (∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
        (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
        Γ (t, 0) ∈ Metric.ball (homotopyGridRowChain G 0 (by omega) i).center (G.r / 2)) ∧
      (∀ i < G.N, ∀ z ∈ Metric.ball
        (homotopyGridRowChain G 0 (by omega) (i + 1)).center (G.r / 2),
        (homotopyGridRowChain G 0 (by omega) i).solution z =
          (homotopyGridRowChain G 0 (by omega) (i + 1)).solution z) ∧
      (∀ i ≤ G.N, (homotopyGridRowChain G G.N le_rfl i).center =
        Γ ((i : ℝ) / (G.N : ℝ), 1)) ∧
      (∀ i ≤ G.N, ∀ z ∈ Metric.ball
        (homotopyGridRowChain G G.N le_rfl i).center G.r, ‖H z‖ ≤ G.M) ∧
      (∀ i < G.N, ∀ t ∈ Icc ((i : ℝ) / (G.N : ℝ))
        (((i + 1 : ℕ) : ℝ) / (G.N : ℝ)),
        Γ (t, 1) ∈ Metric.ball (homotopyGridRowChain G G.N le_rfl i).center (G.r / 2)) ∧
      (∀ i < G.N, ∀ z ∈ Metric.ball
        (homotopyGridRowChain G G.N le_rfl (i + 1)).center (G.r / 2),
        (homotopyGridRowChain G G.N le_rfl i).solution z =
          (homotopyGridRowChain G G.N le_rfl (i + 1)).solution z) := by
  have hN := G.N_pos
  have hNr : 0 < (G.N : ℝ) := by exact_mod_cast hN
  have hNdiv : (G.N : ℝ) / (G.N : ℝ) = 1 := div_self hNr.ne'
  -- Unified row helpers valid for any row `j ≤ G.N`
  have hnode_chain (j : ℕ) (hj : j ≤ G.N) (i : ℕ) (hi : i ≤ G.N) :
      (homotopyGridRowChain G j hj i).center = G.node i j := by
    simp [homotopyGridRowChain, homotopyGridRowDisk, Nat.min_eq_left hi, holomorphicDiskSolutionOfBound]
  have hcent (j : ℕ) (hj : j ≤ G.N) (i : ℕ) (hi : i ≤ G.N) :
      (homotopyGridRowChain G j hj i).center = Γ ((i : ℝ) / (G.N : ℝ), (j : ℝ) / (G.N : ℝ)) := by
    rw [hnode_chain j hj i hi, G.node_eq i hi j hj]
  have hinit (j : ℕ) (hj : j ≤ G.N) (i : ℕ) (hi : i ≤ G.N) :
      (homotopyGridRowChain G j hj i).initial =
        finiteGridHorizontal (homotopyGridRight G) 0 j i y := by
    simp [homotopyGridRowChain, homotopyGridRowDisk, Nat.min_eq_left hi, holomorphicDiskSolutionOfBound]
  have hbound (j : ℕ) (hj : j ≤ G.N) (i : ℕ) (hi : i ≤ G.N)
      (z : ℂ) (hz : z ∈ Metric.ball (homotopyGridRowChain G j hj i).center G.r) :
      ‖H z‖ ≤ G.M := by
    rw [hnode_chain j hj i hi] at hz
    exact (G.data i hi j hj).bounded z hz
  have hoverlap (j : ℕ) (hj : j ≤ G.N)
      (hdist : ∀ i < G.N, dist (G.node (i + 1) j) (G.node i j) < G.r / 2)
      (i : ℕ) (hi : i < G.N)
      (z : ℂ) (hz : z ∈ Metric.ball (homotopyGridRowChain G j hj (i + 1)).center (G.r / 2)) :
      (homotopyGridRowChain G j hj i).solution z =
        (homotopyGridRowChain G j hj (i + 1)).solution z := by
    set D := homotopyGridRowChain G j hj
    have hi' := hi.le; have hi1 := Nat.succ_le_iff.mpr hi
    have hc0 := hnode_chain j hj i hi'
    have hc1 := hnode_chain j hj (i + 1) hi1
    have hnext : (D (i + 1)).initial = (D i).solution (G.node (i + 1) j) := by
      simp [D, homotopyGridRowChain, homotopyGridRowDisk, Nat.min_eq_left hi',
        holomorphicDiskSolutionOfBound, finiteGridHorizontal, homotopyGridRight,
        localPicardTransfer, hi, hj]
    have hprevBall : Metric.ball (D (i + 1)).center (G.r / 2) ⊆ Metric.ball (D i).center G.r :=
      fun w hw => by
        rw [Metric.mem_ball, hc0]; rw [Metric.mem_ball, hc1] at hw
        exact (dist_triangle w (G.node (i + 1) j) (G.node i j)).trans_lt
          ((add_lt_add hw (hdist i hi)).trans_eq (add_halves G.r))
    exact holomorphic_linear_system_solution_unique_of_eq_at
      (D (i + 1)).center (G.r / 2) G.M H G.M_nonneg
      (fun w hw => hbound j hj (i + 1) hi1 w (Metric.ball_subset_ball (by linarith [G.r_pos]) hw))
      (fun w hw => (D i).derivative w (hprevBall hw))
      (fun w hw => (D (i + 1)).derivative w (Metric.ball_subset_ball (by linarith [G.r_pos]) hw))
      (Metric.mem_ball_self (half_pos G.r_pos)) hz
      (by rw [hc1, ← hnext, ← hc1, (D (i + 1)).solution_center])
  -- Bottom (j = 0) and top (j = G.N) instantiations
  let Db := homotopyGridRowChain G 0 (Nat.zero_le _)
  let Dt := homotopyGridRowChain G G.N le_rfl
  have hbc (i : ℕ) (hi : i ≤ G.N) : (Db i).center = Γ ((i : ℝ) / (G.N : ℝ), 0) := by
    simpa [Db] using hcent 0 (Nat.zero_le _) i hi
  have htc (i : ℕ) (hi : i ≤ G.N) : (Dt i).center = Γ ((i : ℝ) / (G.N : ℝ), 1) := by
    simpa [Dt, hNdiv] using hcent G.N le_rfl i hi
  have hbcover (i : ℕ) (hi : i < G.N) (t : ℝ)
      (ht : t ∈ Icc ((i : ℝ) / (G.N : ℝ)) (((i + 1 : ℕ) : ℝ) / (G.N : ℝ))) :
      Γ (t, 0) ∈ Metric.ball (Db i).center (G.r / 2) := by
    rw [Metric.mem_ball, hbc i hi.le]
    have hn := G.cell_image i hi 0 hN t ht 0 ⟨by norm_num, by positivity⟩
    simp only [Nat.cast_zero, zero_div] at hn
    exact hn.trans_le (by linarith [G.r_pos])
  have hlast : G.N - 1 < G.N := Nat.sub_lt hN zero_lt_one
  have hsucc : G.N - 1 + 1 = G.N := Nat.sub_add_cancel hN
  have htcover (i : ℕ) (hi : i < G.N) (t : ℝ)
      (ht : t ∈ Icc ((i : ℝ) / (G.N : ℝ)) (((i + 1 : ℕ) : ℝ) / (G.N : ℝ))) :
      Γ (t, 1) ∈ Metric.ball (Dt i).center (G.r / 2) := by
    rw [Metric.mem_ball, htc i hi.le]
    have h1mem : (1 : ℝ) ∈ Icc (((G.N - 1 : ℕ) : ℝ) / (G.N : ℝ))
        (((G.N - 1 + 1 : ℕ) : ℝ) / (G.N : ℝ)) := by
      rw [hsucc, hNdiv]
      exact ⟨(div_le_one hNr).2 (by exact_mod_cast Nat.sub_le G.N 1), le_rfl⟩
    have hn := G.cell_image i hi (G.N - 1) hlast t ht 1 h1mem
    have hv := (G.cells i hi (G.N - 1) hlast).2.1
    rw [hsucc, G.node_eq i hi.le G.N le_rfl, G.node_eq i hi.le (G.N - 1) hlast.le, hNdiv, dist_comm] at hv
    exact (dist_triangle _ _ _).trans_lt ((add_lt_add hn hv).trans_eq (by ring))
  have hboverlap := hoverlap 0 (Nat.zero_le _) fun i hi =>
    (G.cells i hi 0 hN).1.trans (by linarith [G.r_pos])
  have htoverlap := hoverlap G.N le_rfl fun i hi => by
    have hd := (G.cells i hi (G.N - 1) hlast).2.2
    have hv := (G.cells i hi (G.N - 1) hlast).2.1
    rw [hsucc] at hd hv; rw [dist_comm] at hv
    exact (dist_triangle _ _ _).trans_lt ((add_lt_add hd hv).trans_eq (by ring))
  have hbCont : ContinuousOn (fun t => Γ (t, 0)) (Icc 0 1) :=
    hΓ.comp (by fun_prop) fun t ht => ⟨ht, by norm_num⟩
  have htCont : ContinuousOn (fun t => Γ (t, 1)) (Icc 0 1) :=
    hΓ.comp (by fun_prop) fun t ht => ⟨ht, by norm_num⟩
  obtain ⟨bottom, hbottomCont, hbottomStart, hbottomEnd, hbottomFormula⟩ :=
    exists_continuous_lift_from_disk_chain H hbCont
      G.N hN G.r G.r_pos Db y (by simpa using hbc 0 (Nat.zero_le _)) rfl hbc hbcover hboverlap
  obtain ⟨top, htopCont, htopStart, htopEnd, htopFormula⟩ :=
    exists_continuous_lift_from_disk_chain H htCont
      G.N hN G.r G.r_pos Dt y (by simpa using htc 0 (Nat.zero_le _)) rfl htc htcover htoverlap
  have hendEq : bottom 1 = top 1 := by
    rw [hbottomEnd, htopEnd]
    have hbN : (Db G.N).center = Γ (1, 0) := by simpa [hNdiv] using hbc G.N le_rfl
    have htN : (Dt G.N).center = Γ (1, 1) := by simpa [hNdiv] using htc G.N le_rfl
    rw [← hbN, (Db G.N).solution_center, ← htN, (Dt G.N).solution_center,
      hinit 0 (Nat.zero_le _) G.N le_rfl, hinit G.N le_rfl G.N le_rfl]
    exact G.transfer_eq
  exact ⟨bottom, top, hbottomCont, htopCont, hbottomStart, htopStart, hendEq,
    hbottomFormula, htopFormula, hbc, hbound 0 (Nat.zero_le _), hbcover, hboverlap,
    htc, hbound G.N le_rfl, htcover, htoverlap⟩

end DOZZ.Proofs
