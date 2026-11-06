/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.LiftUniqueness
public import DOZZ.Hypergeom.ODE.PathLift

/-! A finite Picard chain gives local holomorphic charts for its continuous path lift. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The continuous lift associated with a finite disk chain is locally represented by one of the
chain's holomorphic solutions, including at subdivision nodes. -/
theorem disk_chain_lift_has_path_solution_charts
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (N : ℕ) (hN : 0 < N) r M (hr : 0 < r) (hM : 0 ≤ M)
    (H : ℂ → E →L[ℂ] E)
    (D : ℕ → HolomorphicDiskSolution H r)
    (hcenters : ∀ i ≤ N, (D i).center = γ ((i : ℝ) / (N : ℝ)))
    (hbound : ∀ i ≤ N, ∀ z ∈ Metric.ball (D i).center r, ‖H z‖ ≤ M)
    (hcover : ∀ i < N, ∀ s ∈ Icc ((i : ℝ) / (N : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
      γ s ∈ Metric.ball (D i).center (r / 2))
    (hoverlap : ∀ i < N, ∀ z ∈ Metric.ball (D (i + 1)).center (r / 2),
      (D i).solution z = (D (i + 1)).solution z)
    {F : ℝ → E}
    (hformula : ∀ i < N, ∀ s ∈ Icc ((i : ℝ) / (N : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
      F s = (D i).solution (γ s)) :
    ∀ t ∈ Icc (0 : ℝ) 1, Nonempty (PathSolutionChart γ H F t) := by
  intro t ht
  obtain ⟨i, hi, hleft, hright, hright'⟩ := exists_equal_subdivision_interval N hN ht
  let τ : ℕ → ℝ := fun j => (j : ℝ) / (N : ℝ)
  let lo : ℝ := τ i
  let up : ℝ := τ (i + 1)
  let gap : ℝ := 1 / (N : ℝ)
  have hleft' : lo ≤ t := by simpa [lo, τ] using hleft
  have hright'' : t ≤ up := by simpa [up, τ] using hright
  have hstep j : τ (j + 1) = τ j + gap := by
    dsimp [τ, gap]
    rw [Nat.cast_add]
    ring
  have : (D i).center = γ lo := by simpa [lo, τ] using hcenters i (Nat.le_of_lt hi)
  have hpointCover := hcover i hi t ⟨hleft', hright''⟩
  obtain ⟨δγ, hδγ, hγclose⟩ :=
    (Metric.continuousWithinAt_iff.mp (hγ.continuousWithinAt ht)) (r / 2) (by linarith)
  let localChart : PathSolutionChart γ H F t := {
    radius := r / 2
    radius_pos := by linarith
    bound := M
    bound_nonneg := hM
    solution := (D i).solution
    coefficient_bound := by
      intro z hz
      have hzCenter : z ∈ Metric.ball (D i).center r := by
        rw [Metric.mem_ball] at hz ⊢
        calc
          dist z (D i).center ≤ dist z (γ t) + dist (γ t) (D i).center := dist_triangle _ _ _
          _ < r / 2 + r / 2 := add_lt_add hz (Metric.mem_ball.mp hpointCover)
          _ = r := by ring
      exact hbound i (Nat.le_of_lt hi) z hzCenter
    derivative := by
      intro z hz
      have hzCenter : z ∈ Metric.ball (D i).center r := by
        rw [Metric.mem_ball] at hz ⊢
        calc
          dist z (D i).center ≤ dist z (γ t) + dist (γ t) (D i).center := dist_triangle _ _ _
          _ < r / 2 + r / 2 := add_lt_add hz (Metric.mem_ball.mp hpointCover)
          _ = r := by ring
      exact (D i).derivative z hzCenter
    local_agrees := by
      by_cases htl : t = lo
      · subst t
        refine ⟨min δγ gap, lt_min hδγ (show 0 < gap by dsimp [gap]; positivity), ?_⟩
        intro s hs hst
        have hstGap : dist s lo < gap := lt_of_lt_of_le hst (min_le_right _ _)
        have hnear : lo - gap < s ∧ s < lo + gap := by
          rw [Real.dist_eq] at hstGap
          have := abs_lt.mp hstGap
          constructor <;> linarith
        have hup_eq : up = lo + gap := by
          dsimp [up, lo]
          rw [hstep]
        by_cases hsle : s ≤ lo
        · by_cases hizero : i = 0
          · have hlozero : lo = 0 := by simp [lo, τ, hizero]
            exact hformula i hi s (by simpa [lo, up, τ] using (show s ∈ Icc lo up by rw [hup_eq]; exact ⟨(by simpa [hlozero] using hs.1), le_of_lt hnear.2⟩))
          · let j := i - 1
            have hjSucc : j + 1 = i := by dsimp [j]; omega
            have hjlt : j < N := by omega
            have hjlo : τ j = lo - gap := by
              dsimp [lo]
              rw [← hjSucc]
              linarith [(hstep j)]
            calc
              F s = (D j).solution (γ s) := (hformula j hjlt s (by simpa [τ] using (show s ∈ Icc (τ j) (τ (j + 1)) by rw [hjSucc]; exact (by rw [hjlo]; exact ⟨le_of_lt hnear.1, hsle⟩))))
              _ = (D i).solution (γ s) := by simpa [hjSucc] using (hoverlap j hjlt (γ s) (by rw [Metric.mem_ball, (show (D (j + 1)).center = γ lo by rw [hjSucc]; simpa [lo] using hcenters i (Nat.le_of_lt hi))]; exact (hγclose hs (lt_of_lt_of_le hst (min_le_left _ _)))))
        · have hslo : lo ≤ s := le_of_not_ge hsle
          exact hformula i hi s (by simpa [lo, up, τ] using (show s ∈ Icc lo up by rw [hup_eq]; exact ⟨hslo, le_of_lt hnear.2⟩))
      · have hlo : lo < t := lt_of_le_of_ne hleft' (fun h => htl h.symm)
        by_cases hEnd : t = 1
        · have hsuccN : i + 1 ≤ N := Nat.succ_le_iff.mpr hi
          refine ⟨min δγ (t - lo), lt_min hδγ (by linarith), ?_⟩
          intro s hs hst
          have hstTime : dist s t < t - lo := lt_of_lt_of_le hst (min_le_right _ _)
          have hnear : lo < s := by
            rw [Real.dist_eq] at hstTime
            have := abs_lt.mp hstTime
            linarith
          exact hformula i hi s (by simpa [lo, up, τ] using (show s ∈ Icc lo up by rw [(le_antisymm (by dsimp [up, τ]; apply (div_le_one (by exact_mod_cast hN)).2; exact_mod_cast hsuccN) (by simpa [hEnd] using hright'') : up = 1)]; exact ⟨hnear.le, by simpa [hEnd] using hs.2⟩))
        · have hup : t < up := (show t < up ∨ t = 1 by simpa [up, τ] using hright').resolve_right hEnd
          let δtime := min (t - lo) (up - t)
          refine ⟨min δγ δtime, lt_min hδγ (lt_min (by linarith) (by linarith)), ?_⟩
          intro s hs hst
          have : dist (γ s) (γ t) < r / 2 := hγclose hs (lt_of_lt_of_le hst (min_le_left _ _))
          have hstTime : dist s t < δtime := lt_of_lt_of_le hst (min_le_right _ _)
          have hnear : lo < s ∧ s < up := by
            rw [Real.dist_eq] at hstTime
            have := abs_lt.mp hstTime
            constructor
            · have hmin : δtime ≤ t - lo := min_le_left _ _
              linarith
            · have hmin : δtime ≤ up - t := min_le_right _ _
              linarith
          exact hformula i hi s (by simpa [lo, up, τ] using (⟨hnear.1.le, hnear.2.le⟩ : s ∈ Icc lo up))
  }
  exact ⟨localChart⟩

end DOZZ.Proofs
