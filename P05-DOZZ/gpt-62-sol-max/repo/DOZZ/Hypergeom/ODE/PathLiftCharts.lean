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

/-- A finite Picard continuation of the initial value `y` along `γ`, including its local disk data
and continuous path lift. -/
structure PathContinuationLift (γ : ℝ → ℂ) (H : ℂ → E →L[ℂ] E) (y : E) where
  subdivision : ℕ
  subdivision_pos : 0 < subdivision
  radius : ℝ
  coefficient_bound : ℝ
  radius_pos : 0 < radius
  coefficient_bound_nonneg : 0 ≤ coefficient_bound
  disks : ℕ → HolomorphicDiskSolution H radius
  disks_initial : (disks 0).initial = y
  centers : ∀ i ≤ subdivision,
    (disks i).center = γ ((i : ℝ) / (subdivision : ℝ))
  operator_bound : ∀ i ≤ subdivision, ∀ z ∈ Metric.ball (disks i).center radius,
    ‖H z‖ ≤ coefficient_bound
  path_cover : ∀ i < subdivision, ∀ t ∈ Icc ((i : ℝ) / (subdivision : ℝ))
    (((i + 1 : ℕ) : ℝ) / (subdivision : ℝ)),
    γ t ∈ Metric.ball (disks i).center (radius / 2)
  overlap : ∀ i < subdivision, ∀ z ∈ Metric.ball (disks (i + 1)).center (radius / 2),
    (disks i).solution z = (disks (i + 1)).solution z
  value : ℝ → E
  value_continuous : ContinuousOn value (Icc (0 : ℝ) 1)
  value_initial : value 0 = y
  local_formula : ∀ i < subdivision, ∀ t ∈ Icc ((i : ℝ) / (subdivision : ℝ))
    (((i + 1 : ℕ) : ℝ) / (subdivision : ℝ)),
    value t = (disks i).solution (γ t)

/-- A finite-chain lift is locally represented by a disk solution, including at subdivision nodes. -/
theorem path_continuation_lift_has_solution_charts
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {H : ℂ → E →L[ℂ] E} {y : E} (A : PathContinuationLift γ H y) :
    ∀ t ∈ Icc (0 : ℝ) 1, Nonempty (PathSolutionChart γ H A.value t) := by
  obtain ⟨N, hN, r, M, hr, hM, D, _, hcenters, hbound, hcover, hoverlap, F, _, _, hformula⟩ := A
  intro t ht
  obtain ⟨i, hi, hleft, hright, hright'⟩ := exists_equal_subdivision_interval N hN ht
  let τ : ℕ → ℝ := fun j => (j : ℝ) / (N : ℝ)
  let lo : ℝ := τ i
  let up : ℝ := τ (i + 1)
  let gap : ℝ := 1 / (N : ℝ)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hgap : 0 < gap := by dsimp [gap]; positivity
  have hleft' : lo ≤ t := by simpa [lo, τ] using hleft
  have hright'' : t ≤ up := by simpa [up, τ] using hright
  have hrightStrict : t < up ∨ t = 1 := by
    simpa [up, τ] using hright'
  have hstep (j : ℕ) : τ (j + 1) = τ j + gap := by
    dsimp [τ, gap]
    rw [Nat.cast_add]
    ring
  have hiCenter : (D i).center = γ lo := by simpa [lo, τ] using hcenters i (Nat.le_of_lt hi)
  have hpointCover : γ t ∈ Metric.ball (D i).center (r / 2) :=
    hcover i hi t ⟨hleft', hright''⟩
  obtain ⟨δγ, hδγ, hγclose⟩ :=
    (Metric.continuousWithinAt_iff.mp (hγ.continuousWithinAt ht)) (r / 2) (by linarith)
  have hball : Metric.ball (γ t) (r / 2) ⊆ Metric.ball (D i).center r := by
    refine Metric.ball_subset_ball' ?_
    have hd := Metric.mem_ball.mp hpointCover
    linarith
  let localChart : PathSolutionChart γ H F t := {
    radius := r / 2
    radius_pos := by linarith
    bound := M
    bound_nonneg := hM
    solution := (D i).solution
    coefficient_bound := fun z hz => hbound i hi.le z (hball hz)
    derivative := fun z hz => (D i).derivative z (hball hz)
    local_agrees := by
      by_cases htl : t = lo
      · subst t
        refine ⟨min δγ gap, lt_min hδγ hgap, ?_⟩
        intro s hs hst
        have hstγ : dist s lo < δγ := lt_of_lt_of_le hst (min_le_left _ _)
        have hγs : dist (γ s) (γ lo) < r / 2 := hγclose hs hstγ
        have hstGap : dist s lo < gap := lt_of_lt_of_le hst (min_le_right _ _)
        have hnear : lo - gap < s ∧ s < lo + gap := by
          rw [Real.dist_eq] at hstGap
          have habs := abs_lt.mp hstGap
          constructor <;> linarith
        have hup_eq : up = lo + gap := by
          dsimp [up, lo]
          rw [hstep]
        by_cases hsle : s ≤ lo
        · by_cases hizero : i = 0
          · have hlozero : lo = 0 := by simp [lo, τ, hizero]
            have hslo : lo ≤ s := by simpa [hlozero] using hs.1
            have hseg : s ∈ Icc lo up := by
              rw [hup_eq]
              exact ⟨hslo, le_of_lt hnear.2⟩
            exact hformula i hi s (by simpa [lo, up, τ] using hseg)
          · let j := i - 1
            have hjSucc : j + 1 = i := by dsimp [j]; omega
            have hjlt : j < N := by omega
            have hjstep : τ (j + 1) = τ j + gap := hstep j
            have hjlo : τ j = lo - gap := by
              dsimp [lo]
              rw [← hjSucc]
              linarith [hjstep]
            have hprevSeg : s ∈ Icc (τ j) lo := by
              rw [hjlo]
              exact ⟨le_of_lt hnear.1, hsle⟩
            have hprevSeg' : s ∈ Icc (τ j) (τ (j + 1)) := by
              rw [hjSucc]
              exact hprevSeg
            have hprev := hformula j hjlt s (by simpa [τ] using hprevSeg')
            have hnextCenter : (D (j + 1)).center = γ lo := by
              rw [hjSucc]
              simpa [lo] using hcenters i (Nat.le_of_lt hi)
            have hγball : γ s ∈ Metric.ball (D (j + 1)).center (r / 2) := by
              rw [Metric.mem_ball, hnextCenter]
              exact hγs
            have hover := hoverlap j hjlt (γ s) hγball
            calc
              F s = (D j).solution (γ s) := hprev
              _ = (D i).solution (γ s) := by simpa [hjSucc] using hover
        · have hslo : lo ≤ s := le_of_not_ge hsle
          have hseg : s ∈ Icc lo up := by
            rw [hup_eq]
            exact ⟨hslo, le_of_lt hnear.2⟩
          exact hformula i hi s (by simpa [lo, up, τ] using hseg)
      · have hlo : lo < t := lt_of_le_of_ne hleft' (fun h => htl h.symm)
        by_cases hEnd : t = 1
        · have hsuccN : i + 1 ≤ N := Nat.succ_le_iff.mpr hi
          have hupLe : up ≤ 1 := by
            dsimp [up, τ]
            apply (div_le_one hNreal).2
            exact_mod_cast hsuccN
          have hupEq : up = 1 := le_antisymm hupLe (by simpa [hEnd] using hright'')
          refine ⟨min δγ (t - lo), lt_min hδγ (by linarith), ?_⟩
          intro s hs hst
          have hstγ : dist s t < δγ := lt_of_lt_of_le hst (min_le_left _ _)
          have hγs : dist (γ s) (γ t) < r / 2 := hγclose hs hstγ
          have hstTime : dist s t < t - lo := lt_of_lt_of_le hst (min_le_right _ _)
          have hnear : lo < s := by
            rw [Real.dist_eq] at hstTime
            have habs := abs_lt.mp hstTime
            linarith
          have hseg : s ∈ Icc lo up := by
            rw [hupEq]
            exact ⟨hnear.le, by simpa [hEnd] using hs.2⟩
          exact hformula i hi s (by simpa [lo, up, τ] using hseg)
        · have hup : t < up := hrightStrict.resolve_right hEnd
          let δtime := min (t - lo) (up - t)
          have hδtime : 0 < δtime := lt_min (by linarith) (by linarith)
          refine ⟨min δγ δtime, lt_min hδγ hδtime, ?_⟩
          intro s hs hst
          have hstγ : dist s t < δγ := lt_of_lt_of_le hst (min_le_left _ _)
          have hγs : dist (γ s) (γ t) < r / 2 := hγclose hs hstγ
          have hstTime : dist s t < δtime := lt_of_lt_of_le hst (min_le_right _ _)
          have hnear : lo < s ∧ s < up := by
            rw [Real.dist_eq] at hstTime
            have habs := abs_lt.mp hstTime
            constructor
            · have hmin : δtime ≤ t - lo := min_le_left _ _
              linarith
            · have hmin : δtime ≤ up - t := min_le_right _ _
              linarith
          have hseg : s ∈ Icc lo up := ⟨hnear.1.le, hnear.2.le⟩
          exact hformula i hi s (by simpa [lo, up, τ] using hseg)
  }
  exact ⟨localChart⟩

end DOZZ.Proofs
