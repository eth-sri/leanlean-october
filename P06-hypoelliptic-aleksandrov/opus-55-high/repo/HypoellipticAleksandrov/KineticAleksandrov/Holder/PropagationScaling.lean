module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParametersBounds
import Mathlib.Tactic

/-! # Exact dependence of source propagation parameters under dimensional substitution -/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

variable (d : ℕ) (lam Lam b : ℝ) {T : ℝ}

/-- The dimensional substitution preserves the source barrier height and width. -/
theorem propagation_barrier_scaling  (hT : 0 < T) :
    barrierL d lam Lam (b / Real.sqrt T) T = barrierL d lam Lam b 1 ∧
      barrierW d lam Lam (b / Real.sqrt T) T = barrierW d lam Lam b 1 := by
  have hs  := (Real.sqrt_pos.mpr hT).ne'
  have he : (b / Real.sqrt T) ^ 2 * T = b ^ 2 := by
    grind
  have hmul : b / Real.sqrt T * Real.sqrt T = b := div_mul_cancel₀ b hs
  have hL : barrierL d lam Lam (b / Real.sqrt T) T = barrierL d lam Lam b 1 := by
    unfold barrierL XiStar
    grind
  refine ⟨hL, ?_⟩
  unfold barrierW
  grind

/-- Both dimensional tube coefficients equal their normalized counterparts. -/
theorem propagation_tube_scaling  (hT : 0 < T) :
    velocityTubeConstant d lam Lam (b / Real.sqrt T) T =
        velocityTubeConstant d lam Lam b 1 ∧
      positionTubeConstant d lam Lam (b / Real.sqrt T) T =
        positionTubeConstant d lam Lam b 1 := by
  have hW := (propagation_barrier_scaling d lam Lam b hT).2
  have hs  := (Real.sqrt_pos.mpr hT).ne'
  have he : b / Real.sqrt T * Real.sqrt T = b := div_mul_cancel₀ b hs
  constructor
  · unfold velocityTubeConstant
    grind
  · unfold positionTubeConstant
    grind

/-- The complete source step restriction scales linearly with the terminal time. -/
theorem propagation_step_scaling  (lam Lam a b cx cv : ℝ)
    (hb : 0 ≤ b) (hcx : 0 ≤ cx) {T : ℝ} (hT : 0 < T) :
    stepSize d lam Lam (b / Real.sqrt T) (a * T) T
      (cx * T ^ (3 / 2 : ℝ)) (cv * Real.sqrt T) =
      T * stepSize d lam Lam b a 1 cx cv := by
  have hW := (propagation_barrier_scaling d lam Lam b hT).2
  obtain ⟨hc1, hc2⟩ := propagation_tube_scaling d lam Lam b hT
  obtain ⟨_, hc2pos⟩ := tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := 1) hb
  have htime : a * T / barrierW d lam Lam b 1 ^ 2 =
      T * (a / barrierW d lam Lam b 1 ^ 2) := by ring
  have hvel : (cv * Real.sqrt T / (2 * velocityTubeConstant d lam Lam b 1)) ^ 2 =
      T * (cv / (2 * velocityTubeConstant d lam Lam b 1)) ^ 2 := by
    grind
  have hpos : (cx * T ^ (3 / 2 : ℝ) / (2 * positionTubeConstant d lam Lam b 1)) ^
      (2 / 3 : ℝ) = T * (cx / (2 * positionTubeConstant d lam Lam b 1)) ^ (2 / 3 : ℝ) := by
    have he : cx * T ^ (3 / 2 : ℝ) / (2 * positionTubeConstant d lam Lam b 1) =
        (cx / (2 * positionTubeConstant d lam Lam b 1)) * T ^ (3 / 2 : ℝ) := by ring
    rw [he, Real.mul_rpow (div_nonneg hcx (by positivity))
      (Real.rpow_nonneg hT.le _), ← Real.rpow_mul hT.le]
    norm_num
    ring
  unfold stepSize
  rw [hW, hc1, hc2, htime, hvel, hpos, mul_min_of_nonneg _ _ hT.le, mul_min_of_nonneg _ _ hT.le]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
