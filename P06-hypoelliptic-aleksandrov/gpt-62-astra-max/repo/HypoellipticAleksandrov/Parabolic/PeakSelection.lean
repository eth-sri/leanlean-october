module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.Compact

/-!
# Compact weighted peak selection

This file records the terminal-inclusive compact selection used in the
parabolic Krylov--Safonov peak argument.  Its boxes are coordinate cubes.
-/

@[expose] public section

open Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

variable {d : Nat} (m : Nat) (v : PDE.Vec d) (terminalTime : Real) (hm : 0 < m) (v0 : PDE.Vec d)
    (u : TimeVelocity d → Real) (z : TimeVelocity d)

include v in
/-- The coordinate sup norm on a velocity vector. -/
def velocitySupNorm : Real :=
  ↑(Finset.univ.sup fun i : Fin d => ‖v i‖₊)

/-- The terminal-inclusive closed backward parabolic coordinate box. -/
def backwardParabolicClosedBox (r terminalTime : Real)
    (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  Set.Icc (terminalTime - r ^ 2) terminalTime ×ˢ velocityClosedCube v0 r

include terminalTime v0 z in
/-- The backward parabolic radius relative to a terminal time and velocity. -/
def backwardParabolicRadius : Real :=
  max (velocitySupNorm (z.2 - v0)) (Real.sqrt (terminalTime - z.1))

include m terminalTime v0 u z in
/-- The compact-selection weight used by the backward peak argument. -/
def weightedBackwardPeak : Real :=
  (1 - backwardParabolicRadius terminalTime v0 z) ^ m * u z

/-- The coordinate sup norm agrees with the native finite-product norm. -/
theorem velocitySupNorm_eq_norm :
    velocitySupNorm v = ‖v‖ := by
  rfl

/-- Membership in a coordinate cube is precisely a coordinate-sup bound. -/
theorem mem_velocityClosedCube_iff_velocitySupNorm_sub_le
    {v v0 : PDE.Vec d} {r : Real} (hr : 0 ≤ r) :
    v ∈ velocityClosedCube v0 r ↔ velocitySupNorm (v - v0) ≤ r := by
  constructor
  · intro hv
    rw [velocitySupNorm_eq_norm, pi_norm_le_iff_of_nonneg hr]
    intro i
    exact hv i
  · intro hv i
    have hnorm : ‖v - v0‖ ≤ r := by
      exact hv
    have hcoord := (pi_norm_le_iff_of_nonneg hr).mp hnorm i
    exact hcoord

/-- Membership in a terminal-inclusive backward box. -/
theorem mem_backwardParabolicClosedBox_iff {r terminalTime t : Real}
    {v0 v : PDE.Vec d} :
    (t, v) ∈ backwardParabolicClosedBox r terminalTime v0 ↔
      terminalTime - r ^ 2 ≤ t ∧ t ≤ terminalTime ∧ v ∈ velocityClosedCube v0 r := by
  constructor
  · rintro ⟨⟨ht0, ht⟩, hv⟩
    exact ⟨ht0, ht, hv⟩
  · rintro ⟨ht0, ht, hv⟩
    exact ⟨⟨ht0, ht⟩, hv⟩

/-- Terminal-inclusive backward coordinate boxes are compact. -/
theorem isCompact_backwardParabolicClosedBox (r terminalTime : Real)
    (v0 : PDE.Vec d) :
    IsCompact (backwardParabolicClosedBox r terminalTime v0) :=
  isCompact_Icc.prod (isCompact_velocityClosedCube v0 r)

/-- The coordinate sup norm is continuous. -/
theorem continuous_velocitySupNorm :
    Continuous (velocitySupNorm : PDE.Vec d → Real) := by
  exact continuous_norm

/-- The backward parabolic radius is continuous. -/
theorem continuous_backwardParabolicRadius :
    Continuous (backwardParabolicRadius terminalTime v0) := by
  exact (continuous_velocitySupNorm.comp (continuous_snd.sub continuous_const)).max
    (Real.continuous_sqrt.comp (continuous_const.sub continuous_fst))

/-- The backward radius is at most one on the normalized closed unit box. -/
theorem backwardParabolicRadius_le_one_of_mem_unitClosedBox
    {z : TimeVelocity d} (hz : z ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d)) :
    backwardParabolicRadius 4 (0 : PDE.Vec d) z ≤ 1 := by
  rcases (mem_backwardParabolicClosedBox_iff.mp hz) with ⟨htlower, htupper, hv⟩
  apply max_le
  · rw [← mem_velocityClosedCube_iff_velocitySupNorm_sub_le zero_le_one]
    exact hv
  · apply Real.sqrt_le_one.mpr
    linarith

/-- A point in the half-gap box around a radius-`r0` point has radius at most
`(1 + r0) / 2`. -/
theorem backwardParabolicRadius_nested_le {t1 r0 : Real}
    {v1 : PDE.Vec d} (hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 0)
    (hr0 : r0 = backwardParabolicRadius 4 0 (t1, v1)) (hr0lt : r0 < 1)
    {z : TimeVelocity d}
    (hz : z ∈ backwardParabolicClosedBox ((1 - r0) / 2) t1 v1) :
    backwardParabolicRadius 4 0 z ≤ (1 + r0) / 2 := by
  let s := (1 - r0) / 2
  have hs : 0 ≤ s := by
    dsimp [s]
    linarith
  have hr0nonneg : 0 ≤ r0 := by
    rw [hr0, backwardParabolicRadius]
    positivity
  have hv1 : velocitySupNorm v1 ≤ r0 := by
    rw [hr0, backwardParabolicRadius]
    simp
  have ht1 := (mem_backwardParabolicClosedBox_iff.mp hpoint).2.1
  have htime : Real.sqrt (4 - t1) ≤ r0 := by
    rw [hr0, backwardParabolicRadius]
    simp
  have htime_sq : 4 - t1 ≤ r0 ^ 2 := by
    calc
      4 - t1 = Real.sqrt (4 - t1) ^ 2 := (Real.sq_sqrt (sub_nonneg.mpr ht1)).symm
      _ ≤ r0 ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hr0nonneg).mpr htime
  rcases (mem_backwardParabolicClosedBox_iff.mp hz) with ⟨hztime, _, hzvel⟩
  have hzvel' : velocitySupNorm (z.2 - v1) ≤ s := by
    rw [← mem_velocityClosedCube_iff_velocitySupNorm_sub_le hs]
    exact hzvel
  have hspace : velocitySupNorm z.2 ≤ (1 + r0) / 2 := by
    calc
      velocitySupNorm z.2 = ‖z.2‖ := velocitySupNorm_eq_norm _
      _ = ‖(z.2 - v1) + v1‖ := by rw [sub_add_cancel]
      _ ≤ ‖z.2 - v1‖ + ‖v1‖ := norm_add_le _ _
      _ = velocitySupNorm (z.2 - v1) + velocitySupNorm v1 := by
        rw [velocitySupNorm_eq_norm, velocitySupNorm_eq_norm]
      _ ≤ s + r0 := add_le_add hzvel' hv1
      _ = (1 + r0) / 2 := by ring
  have htime_arg : 4 - z.1 ≤ r0 ^ 2 + s ^ 2 := by
    change t1 - s ^ 2 ≤ z.1 at hztime
    nlinarith
  have htime' : Real.sqrt (4 - z.1) ≤ (1 + r0) / 2 := by
    have hsum := add_nonneg hr0nonneg hs
    have hsq : 4 - z.1 ≤ (r0 + s) ^ 2 := by
      nlinarith [sq_nonneg (r0 - s)]
    have hsqrt :=
      (Real.sqrt_le_iff.mpr ⟨hsum, hsq⟩)
    calc
      Real.sqrt (4 - z.1) ≤ r0 + s := hsqrt
      _ = (1 + r0) / 2 := by ring
  change max (velocitySupNorm (z.2 - 0)) (Real.sqrt (4 - z.1)) ≤ (1 + r0) / 2
  simpa using max_le hspace htime'

private theorem terminal_zero_mem_unitClosedBox :
    (4, (0 : PDE.Vec d)) ∈ backwardParabolicClosedBox 1 4 0 := by
  rw [mem_backwardParabolicClosedBox_iff]
  constructor
  · norm_num
  constructor
  · norm_num
  · simp

private theorem backwardParabolicRadius_terminal_zero :
    backwardParabolicRadius 4 (0 : PDE.Vec d) (4, 0) = 0 := by
  simp [backwardParabolicRadius, velocitySupNorm_eq_norm]

include hm in
/-- A continuous function which is positive at the terminal center has a
strictly interior weighted maximizer, together with the exact nested-box bound. -/
theorem exists_weighted_backward_peak
    (hu : ContinuousOn u
      (backwardParabolicClosedBox 1 4 (0 : PDE.Vec d)))
    (hu0 : 0 < u (4, (0 : PDE.Vec d))) :
    ∃ (t1 : Real) (v1 : PDE.Vec d) (r0 : Real),
      (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d) ∧
      r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1) ∧
      (∀ z ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d),
        weightedBackwardPeak m 4 (0 : PDE.Vec d) u z ≤
          weightedBackwardPeak m 4 (0 : PDE.Vec d) u (t1, v1)) ∧
      r0 < 1 ∧
      u (4, (0 : PDE.Vec d)) ≤ (1 - r0) ^ m * u (t1, v1) ∧
      0 < u (t1, v1) ∧
      ∀ z ∈ backwardParabolicClosedBox ((1 - r0) / 2) t1 v1,
        u z ≤ (2 : Real) ^ m * u (t1, v1) := by
  let K : Set (TimeVelocity d) := backwardParabolicClosedBox 1 4 0
  let W := weightedBackwardPeak m 4 0 u
  have hterminal : (4, 0) ∈ K := terminal_zero_mem_unitClosedBox
  have hW : ContinuousOn W K := by
    exact
      ((continuous_const.sub (continuous_backwardParabolicRadius 4 0)).pow m).continuousOn.mul hu
  obtain ⟨z1, hz1, hmax⟩ := (isCompact_backwardParabolicClosedBox 1 4 0).exists_isMaxOn ⟨_, hterminal⟩ hW
  let t1 := z1.1
  let v1 := z1.2
  let r0 := backwardParabolicRadius 4 0 z1
  have hr0le : r0 ≤ 1 := by
    apply backwardParabolicRadius_le_one_of_mem_unitClosedBox <;> assumption
  have hterminal_value : W (4, 0) = u (4, 0) := by
    simp [W, weightedBackwardPeak, backwardParabolicRadius_terminal_zero]
  have hmax_terminal : u (4, 0) ≤ W z1 := by
    rw [← hterminal_value]
    apply hmax <;> assumption
  have hr0lt : r0 < 1 := by
    apply lt_of_le_of_ne hr0le
    intro heq
    have hzero : W z1 = 0 := by
      simp [W, weightedBackwardPeak, r0, heq, hm.ne']
    rw [hzero] at hmax_terminal
    exact (not_lt_of_ge hmax_terminal) hu0
  have hweighted : u (4, 0) ≤ (1 - r0) ^ m * u z1 := by
    exact hmax_terminal
  have hu1 :=
    pos_of_mul_pos_right (hu0.trans_le hweighted) (pow_pos (by linarith) _).le
  refine ⟨t1, v1, r0, ?_, ?_, ?_, hr0lt, ?_, ?_, ?_⟩
  · exact hz1
  · rfl
  · exact hmax
  · exact hweighted
  · exact hu1
  · intro z hz
    have hradius := backwardParabolicRadius_nested_le (d := d)
      (by exact hz1) (by rfl) hr0lt hz
    let s := (1 - r0) / 2
    have hspos : 0 < s := by
      dsimp [s]
      linarith
    have hfactor : s ≤ 1 - backwardParabolicRadius 4 0 z := by
      dsimp [s]
      linarith
    have hfactor_nonneg :=
      hspos.le.trans hfactor
    have hsub : backwardParabolicClosedBox s t1 v1 ⊆ K := by
      intro y hy
      have hy_radius := backwardParabolicRadius_nested_le (d := d)
        (by exact hz1) (by rfl) hr0lt hy
      have hyvel : velocitySupNorm y.2 ≤ 1 := by
        calc
          velocitySupNorm y.2 ≤ backwardParabolicRadius 4 0 y := by
            rw [backwardParabolicRadius]
            simp
          _ ≤ (1 + r0) / 2 := hy_radius
          _ ≤ 1 := by linarith
      have hytime : Real.sqrt (4 - y.1) ≤ 1 := by
        calc
          Real.sqrt (4 - y.1) ≤ backwardParabolicRadius 4 0 y := by
            apply le_max_right
          _ ≤ (1 + r0) / 2 := hy_radius
          _ ≤ 1 := by linarith
      rcases (mem_backwardParabolicClosedBox_iff.mp hy) with ⟨_, hyupper, _⟩
      have ht1upper := (mem_backwardParabolicClosedBox_iff.mp
        (by exact hz1)).2.1
      rw [mem_backwardParabolicClosedBox_iff]
      refine ⟨?_, hyupper.trans ht1upper, ?_⟩
      · linarith [Real.sqrt_le_one.mp hytime]
      · exact (mem_velocityClosedCube_iff_velocitySupNorm_sub_le zero_le_one).mpr (by
          simpa using hyvel)
    by_cases huz : 0 < u z
    · have hpow : s ^ m ≤ (1 - backwardParabolicRadius 4 0 z) ^ m :=
        pow_le_pow_left₀ hspos.le hfactor _
      have hmiddle : s ^ m * u z ≤ (1 - r0) ^ m * u z1 := by
        calc
          s ^ m * u z ≤ (1 - backwardParabolicRadius 4 0 z) ^ m * u z := (mul_le_mul_of_nonneg_right hpow huz.le)
          _ = weightedBackwardPeak m 4 0 u z := rfl
          _ ≤ weightedBackwardPeak m 4 0 u z1 := (hmax (hsub (by simpa [s] using hz)))
          _ = (1 - r0) ^ m * u z1 := by rfl
      apply le_of_mul_le_mul_left (a0 := pow_pos hspos m)
      calc
        s ^ m * u z ≤ (1 - r0) ^ m * u z1 := hmiddle
        _ = s ^ m * (2 ^ m * u z1) := by
          dsimp [s]
          rw [show 1 - r0 = 2 * ((1 - r0) / 2) by ring, mul_pow]
          ring
    · have huzle := le_of_not_gt huz
      have hrightpos : 0 < 2 ^ m * u z1 :=
        mul_pos (pow_pos (by norm_num) _) hu1
      linarith

end

end HypoellipticAleksandrov.Parabolic
