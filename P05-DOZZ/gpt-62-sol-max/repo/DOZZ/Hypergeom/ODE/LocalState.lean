/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.SubtypeLocalPath

/-! Gluing a path-independent endpoint state to its local holomorphic ODE solution. -/

public section

open Set unitInterval

namespace DOZZ.Proofs

section
variable {U : Set ℂ} {x y : U} (p : Path x y)
include U x y

private theorem subtypePathFunction_zero :
    subtypePathFunction p 0 = (x : ℂ) := by
  rw [subtypePathFunction, Set.projIcc_of_mem zero_le_one (by norm_num)]
  exact congrArg Subtype.val p.source

private theorem subtypePathFunction_one :
    subtypePathFunction p 1 = (y : ℂ) := by
  rw [subtypePathFunction, Set.projIcc_of_mem zero_le_one (by norm_num)]
  exact congrArg Subtype.val p.target

end

/-- A path-independent endpoint state agrees locally with the final disk of any lift.
Concatenate with a short straight segment, then use uniqueness on that segment. -/
theorem subtype_path_state_locally_eq_picard
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {U : Set ℂ} (hU : IsOpen U) {H : ℂ → E →L[ℂ] E} (hH : DifferentiableOn ℂ H U)
    {x₀ z : U} {p : Path x₀ z} {y : E} (A : PathContinuationLift (subtypePathFunction p) H y)
    (state : U → E)
    (hstate : ∀ w : U, ∀ {q : Path x₀ w} (B : PathContinuationLift (subtypePathFunction q) H y),
      B.value 1 = state w) :
    ∃ R δ : ℝ, 0 < R ∧ 0 < δ ∧ δ ≤ R / 2 ∧
      ∃ D : HolomorphicDiskSolution H R,
        D.center = (z : ℂ) ∧
          ∀ w : U, dist (w : ℂ) (z : ℂ) < δ → state w = D.solution (w : ℂ) := by
  let R := A.radius
  let D : HolomorphicDiskSolution (H) R := A.disks A.subdivision
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (hU.mem_nhds z.property)
  let ρ := min ε R
  have hρ : 0 < ρ := lt_min hε A.radius_pos
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρR : ρ ≤ R := min_le_right _ _
  have hball : Metric.ball (z : ℂ) ρ ⊆ U := by
    intro u hu
    exact hεball (Metric.ball_subset_ball hρε hu)
  have hNreal : 0 < (A.subdivision : ℝ) := by exact_mod_cast A.subdivision_pos
  have hpEnd := subtypePathFunction_one p
  have hDcenter : D.center = (z : ℂ) := by
    calc
      D.center = subtypePathFunction p
          ((A.subdivision : ℝ) / (A.subdivision : ℝ)) := A.centers A.subdivision le_rfl
      _ = subtypePathFunction p 1 := by rw [div_self hNreal.ne']
      _ = (z : ℂ) := hpEnd
  have hAend : A.value 1 = D.solution (z : ℂ) := by
    calc
      A.value 1 = (A.disks A.subdivision).solution
          (subtypePathFunction p 1) := path_continuation_lift_value_one_eq_final_disk A
      _ = D.solution (z : ℂ) := by rw [hpEnd]
  have hδpos : 0 < ρ / 2 := by linarith
  have hδle : ρ / 2 ≤ R / 2 := by linarith
  refine ⟨R, ρ / 2, A.radius_pos, hδpos, hδle, D, hDcenter, ?_⟩
  intro w hw
  have hw' : dist (z : ℂ) (w : ℂ) < ρ / 2 := by simpa [dist_comm] using hw
  let q := subtypeLocalSegmentPath ρ hρ hball hw'
  let pq := p.trans q
  let γ : ℝ → ℂ := subtypePathFunction pq
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) :=
    (subtypePathFunction_continuous pq).continuousOn
  have hγpath : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U :=
    fun t _ => subtypePathFunction_mem pq t
  obtain ⟨B⟩ := exists_path_continuation_lift hγcont U hU H hH hγpath y
  have hparamLeft : ∀ s ∈ Icc (0 : ℝ) 1, (0 : ℝ) + (1 / 2) * s ∈ Icc (0 : ℝ) 1 := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2]
  obtain ⟨Bpre, hBpreEnd⟩ := exists_path_continuation_lift_affine_reparam
    hγcont U hU hH
    hγpath B (by norm_num) hparamLeft
  have hprePath : ∀ s ∈ Icc (0 : ℝ) 1,
      γ ((0 : ℝ) + (1 / 2) * s) = subtypePathFunction p s := by
    intro s hs
    have harg : (0 : ℝ) + (1 / 2) * s = s / 2 := by ring
    rw [harg]
    change subtypePathFunction pq (s / 2) = _
    exact subtypePathFunction_trans_left p q hs
  let BprePath := path_continuation_lift_congr Bpre hprePath
  let BpreBase := path_continuation_lift_initial_congr BprePath B.value_initial
  have hBpreState := hstate z BpreBase
  have hBmidState : B.value (1 / 2) = state z := by
    calc
      B.value (1 / 2) = Bpre.value 1 := by simpa using hBpreEnd.symm
      _ = BpreBase.value 1 := rfl
      _ = state z := hBpreState
  have hBmidD : B.value (1 / 2) = D.solution (z : ℂ) :=
    hBmidState.trans ((hstate z A).symm.trans hAend)
  have hparamRight : ∀ s ∈ Icc (0 : ℝ) 1,
      (1 / 2 : ℝ) + (1 / 2) * s ∈ Icc (0 : ℝ) 1 := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2]
  obtain ⟨Bpost, hBpostEnd⟩ := exists_path_continuation_lift_affine_reparam
    hγcont U hU hH
    hγpath B (by norm_num) hparamRight
  have hpostPath : ∀ s ∈ Icc (0 : ℝ) 1,
      γ ((1 / 2 : ℝ) + (1 / 2) * s) = subtypePathFunction q s := by
    intro s hs
    have harg : (1 / 2 : ℝ) + (1 / 2) * s = 1 / 2 + s / 2 := by ring
    rw [harg]
    change subtypePathFunction pq (1 / 2 + s / 2) = _
    exact subtypePathFunction_trans_right p q hs
  let BpostPath := path_continuation_lift_congr Bpost hpostPath
  let BpostLocal := path_continuation_lift_initial_congr BpostPath hBmidD
  let qfun : ℝ → ℂ := subtypePathFunction q
  let F : ℝ → E := fun s => D.solution (qfun s)
  have hqcont : ContinuousOn qfun (Icc (0 : ℝ) 1) :=
    (subtypePathFunction_continuous q).continuousOn
  have hρhalf : ρ / 2 ≤ R := by linarith
  have hqhalf : ∀ s ∈ Icc (0 : ℝ) 1, dist (qfun s) (z : ℂ) < ρ / 2 := by
    intro s hs
    have hdist := subtypeLocalSegmentPath_mem_halfBall ρ hρ hball hw'
      (⟨s, hs⟩ : unitInterval)
    simpa only [qfun, subtypePathFunction, (Set.projIcc_of_mem zero_le_one hs)] using hdist
  have hqball : ∀ s ∈ Icc (0 : ℝ) 1, qfun s ∈ Metric.ball (z : ℂ) R := by
    intro s hs
    apply Metric.mem_ball.mpr
    exact lt_of_lt_of_le (hqhalf s hs) hρhalf
  have hDcont : ContinuousOn D.solution (Metric.ball (z : ℂ) R) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    exact (D.derivative u (by simpa [hDcenter] using hu)).continuousAt
  have hFcont : ContinuousOn F (Icc (0 : ℝ) 1) := by
    exact hDcont.comp hqcont hqball
  have hFchart : ∀ s ∈ Icc (0 : ℝ) 1,
      Nonempty (PathSolutionChart qfun (H) F s) := by
    intro s hs
    have hsub : Metric.ball (qfun s) (R / 2) ⊆ Metric.ball D.center R := by
      intro u hu
      rw [hDcenter, Metric.mem_ball] at ⊢
      calc
        dist u (z : ℂ) ≤ dist u (qfun s) + dist (qfun s) (z : ℂ) := dist_triangle _ _ _
        _ < R / 2 + ρ / 2 := add_lt_add_of_lt_of_le (Metric.mem_ball.mp hu) (hqhalf s hs).le
        _ ≤ R := by linarith
    let C : PathSolutionChart qfun H F s := {
      radius := R / 2
      radius_pos := by linarith
      bound := A.coefficient_bound
      bound_nonneg := A.coefficient_bound_nonneg
      solution := D.solution
      coefficient_bound := fun u hu => A.operator_bound A.subdivision le_rfl u (hsub hu)
      derivative := fun u hu => D.derivative u (hsub hu)
      local_agrees := by
        refine ⟨1, by norm_num, ?_⟩
        intro s' hs' hdist
        rfl
    }
    exact ⟨C⟩
  have hstart : F 0 = BpostLocal.value 0 := by
    rw [BpostLocal.value_initial]
    exact congrArg D.solution (subtypePathFunction_zero q)
  have hBpostCharts := path_continuation_lift_has_solution_charts hqcont BpostLocal
  have hpostEq := continuous_path_solution_lifts_unique hqcont
    (H) hFcont BpostLocal.value_continuous hFchart hBpostCharts hstart
  have hlocalEnd : B.value 1 = D.solution (w : ℂ) := by
    calc
      B.value 1 = Bpost.value 1 := by
        have hhalf : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
        calc
          B.value 1 = B.value ((1 / 2 : ℝ) + 1 / 2) := congrArg B.value hhalf.symm
          _ = Bpost.value 1 := hBpostEnd.symm
      _ = BpostLocal.value 1 := rfl
      _ = F 1 := (hpostEq 1 (by norm_num)).symm
      _ = D.solution (w : ℂ) := congrArg D.solution (subtypePathFunction_one q)
  have hBglobal := hstate w B
  calc
    state w = B.value 1 := hBglobal.symm
    _ = D.solution (w : ℂ) := hlocalEnd

end DOZZ.Proofs
