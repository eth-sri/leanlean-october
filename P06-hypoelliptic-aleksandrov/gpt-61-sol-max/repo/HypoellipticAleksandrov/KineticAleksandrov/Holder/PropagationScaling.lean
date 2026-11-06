module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParametersBounds
import Mathlib.Tactic

/-! # Exact dependence of source propagation parameters under dimensional substitution -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- The dimensional substitution preserves the source barrier height and width. -/
theorem propagation_barrier_scaling (d : ℕ) (lam Lam b : ℝ) {T : ℝ} (hT : 0 < T) :
    barrierL d lam Lam (b / Real.sqrt T) T = barrierL d lam Lam b 1 ∧
      barrierW d lam Lam (b / Real.sqrt T) T = barrierW d lam Lam b 1 := by
  have hs  := (Real.sqrt_pos.mpr hT).ne'
  have he : (b / Real.sqrt T) ^ 2 * T = b ^ 2 := by
    rw [div_pow]
    calc
      _ = (b ^ 2 / (Real.sqrt T) ^ 2) * (Real.sqrt T) ^ 2 := by
        rw [Real.sq_sqrt hT.le]
      _ = b ^ 2 := div_mul_cancel₀ _ (pow_ne_zero 2 hs)

  have hL : barrierL d lam Lam (b / Real.sqrt T) T = barrierL d lam Lam b 1 := by
    unfold barrierL XiStar
    rw [mul_assoc 2 ((b / Real.sqrt T) ^ 2) T, he]
    simp only [mul_one]
  refine ⟨hL, ?_⟩
  unfold barrierW
  rw [hL]
  have he' : 2 * (b / Real.sqrt T) * Real.sqrt T = 2 * b := by
    rw [mul_assoc, (div_mul_cancel₀ b hs)]
  rw [he']
  simp only [Real.sqrt_one, mul_one]

variable (d : ℕ)

/-- Both dimensional tube coefficients equal their normalized counterparts. -/
theorem propagation_tube_scaling  (lam Lam b : ℝ) {T : ℝ} (hT : 0 < T) :
    velocityTubeConstant d lam Lam (b / Real.sqrt T) T =
        velocityTubeConstant d lam Lam b 1 ∧
      positionTubeConstant d lam Lam (b / Real.sqrt T) T =
        positionTubeConstant d lam Lam b 1 := by
  have hW := (propagation_barrier_scaling d lam Lam b hT).2

  have he  := div_mul_cancel₀ b ((Real.sqrt_pos.mpr hT).ne')
  constructor
  · unfold velocityTubeConstant
    rw [hW]
    simp only [Real.sqrt_one, mul_one]
    have hm : b / Real.sqrt T * barrierW d lam Lam b 1 ^ 2 * Real.sqrt T =
        b * barrierW d lam Lam b 1 ^ 2 := by
      calc
        _ = (b / Real.sqrt T * Real.sqrt T) * barrierW d lam Lam b 1 ^ 2 := by ring
        _ = _ := by rw [he]
    rw [hm]
  · unfold positionTubeConstant
    rw [hW]
    simp only [Real.sqrt_one, mul_one]
    have hm : b / Real.sqrt T * barrierW d lam Lam b 1 ^ 4 * Real.sqrt T =
        b * barrierW d lam Lam b 1 ^ 4 := by
      calc
        _ = (b / Real.sqrt T * Real.sqrt T) * barrierW d lam Lam b 1 ^ 4 := by ring
        _ = _ := by rw [he]
    rw [hm]

/-- The complete source step restriction scales linearly with the terminal time. -/
theorem propagation_step_scaling  (lam Lam a b cx cv : ℝ)
    (hb : 0 ≤ b) (hcx : 0 ≤ cx) {T : ℝ} (hT : 0 < T) :
    stepSize d lam Lam (b / Real.sqrt T) (a * T) T
      (cx * T ^ (3 / 2 : ℝ)) (cv * Real.sqrt T) =
      T * stepSize d lam Lam b a 1 cx cv := by
  let sharedTerm_8265f81279 := (cx * T ^ (3 / 2 : ℝ) / (2 * positionTubeConstant d lam Lam b 1))
  let sharedTerm_88cab37ca2 := (cx / (2 * positionTubeConstant d lam Lam b 1))

  obtain ⟨hc1, hc2⟩ := propagation_tube_scaling d lam Lam b hT
  obtain ⟨_, hc2pos⟩ := tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := 1) hb
  have htime : a * T / barrierW d lam Lam b 1 ^ 2 =
      T * (a / barrierW d lam Lam b 1 ^ 2) := by ring
  have hvel : (cv * Real.sqrt T / (2 * velocityTubeConstant d lam Lam b 1)) ^ 2 =
      T * (cv / (2 * velocityTubeConstant d lam Lam b 1)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hT.le]
    ring
  have hpos : (sharedTerm_8265f81279) ^
      (2 / 3 : ℝ) = T * (sharedTerm_88cab37ca2) ^ (2 / 3 : ℝ) := by
    have he : sharedTerm_8265f81279 =
        (sharedTerm_88cab37ca2) * T ^ (3 / 2 : ℝ) := by ring
    rw [he, Real.mul_rpow (div_nonneg hcx (by positivity))
      (Real.rpow_nonneg hT.le _), ← Real.rpow_mul hT.le]
    norm_num
    ring
  unfold stepSize
  rw [((propagation_barrier_scaling d lam Lam b hT).2), hc1, hc2, htime, hvel, hpos]
  rw [mul_min_of_nonneg _ _ hT.le, mul_min_of_nonneg _ _ hT.le]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
