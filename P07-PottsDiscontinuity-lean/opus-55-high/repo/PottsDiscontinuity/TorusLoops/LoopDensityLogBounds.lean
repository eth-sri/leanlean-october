module

public import PottsDiscontinuity.TorusLoops.LoopDensityExpectation
public import PottsDiscontinuity.TorusLoops.LoopDensityExponentialTail

/-!
# Logarithmic rate bounds for the weighted loop observable

The expectation truncation bounds and exponentially small weighted tail give a
uniform estimate for the absolute logarithmic rate at every sufficiently large
even width.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC

variable {N : ℕ}

noncomputable section

/-- The expectation's logarithmic rate along positive even widths `M=2(n+1)`. -/
noncomputable def windingLoopDensityLogRate
    (hN : Even N) (hNp : 0 < N) (q : Set.Ici (1 : ℝ)) (n : ℕ) : ℝ := by
  let M := 2 * (n + 1)
  let hM : Even M := by grind
  let hMp : 0 < M := by omega
  exact Real.log (phi_T_windingLoopDensityExpectation hN hM hNp hMp q) / (M : ℝ)

/-- Constant contribution of the two finite factors in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogOffset (q : Set.Ici (1 : ℝ)) : ℝ :=
  Real.log 2 + Real.log (2 * q.val)

section
variable (q : Set.Ici (1 : ℝ))
/-- Coefficient of the truncated loop count in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogSlope  : ℝ :=
  Real.log (windingLoopDensityUpperBase q) - Real.log (windingLoopDensityLowerBase q)

theorem windingLoopDensityLogOffset_nonneg  :
    0 ≤ windingLoopDensityLogOffset q := by
  have hq : (1 : ℝ) ≤ q.val := q.property
  exact add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by nlinarith))

theorem windingLoopDensityLogSlope_nonneg  :
    0 ≤ windingLoopDensityLogSlope q := by
  have hU :=
    Real.log_nonneg (windingLoopDensityUpperBase_ge_one q)
  have hD :=
    Real.log_nonpos (windingLoopDensityLowerBase_pos q).le
      (windingLoopDensityLowerBase_le_one q)
  unfold windingLoopDensityLogSlope
  linarith
end

/-- Once the one-arm input meets the exponential-tail threshold, the absolute
logarithmic rate has the stated finite-size bound. -/
theorem abs_windingLoopDensityLogRate_le
    (hN : Even N) (hNp : 0 < N) (q : Set.Ici (1 : ℝ))
    (r n : ℕ) (hr : 0 < r)
    (hNle : N ≤ 2 * (n + 1))
    (hthreshold : 9 * N ≤ (n + 1) / r + 1)
    (harm : rectangleFreeOneArmProbability q (N / 2 - 1) ≤
      windingLoopTailArmThreshold q r) :
    |windingLoopDensityLogRate hN hNp q n| ≤
      windingLoopDensityLogSlope q / (2 * (r : ℝ)) +
        (windingLoopDensityLogOffset q + windingLoopDensityLogSlope q) /
          (2 * ((n + 1 : ℕ) : ℝ)) := by
  have hM : Even (2 * (n + 1)) := ⟨n + 1, by omega⟩
  have hMp : 0 < 2 * (n + 1) := by omega
  have hU := windingLoopDensityUpperBase_ge_one q
  have hD := windingLoopDensityLowerBase_pos q
  have hq : (1 : ℝ) ≤ q := q.2
  have hP := torusRCProbability_nonneg hN hM q (windingLoopTailEvent hN hM hNp hMp ((n + 1) / r + 1))
  have h16 : (1 / 16 : ℝ) ^ (n + 1) ≤ 1 / 16 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have htail := phi_T_windingLoopDensityWeightedTail_le_pow hN hNp q r (n + 1) hr hNle hthreshold harm
  have h1 := mul_le_mul_of_nonneg_right (one_le_pow₀ (n := N + 2 * (n + 1)) hU) hP
  have hE := phi_T_windingLoopDensityExpectation_pos hN hM hNp hMp q
  have hup := Real.log_le_log hE <| (phi_T_windingLoopDensityExpectation_le_tail hN hM hNp hMp q
    ((n + 1) / r + 1)).trans (by linarith [one_le_pow₀ (n := (n + 1) / r + 1) hU] :
      _ ≤ 2 * windingLoopDensityUpperBase q ^ ((n + 1) / r + 1))
  have hlow := Real.log_le_log (by positivity) <| (mul_le_mul_of_nonneg_left (by linarith : (1 / 2 : ℝ) ≤ _)
    (by positivity)).trans (phi_T_windingLoopDensityExpectation_ge_tail hN hM hNp hMp q ((n + 1) / r + 1))
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hup
  rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity), Real.log_pow, one_div, Real.log_inv] at hlow
  have hU' := Real.log_nonneg hU
  have hD' := Real.log_nonpos hD.le (windingLoopDensityLowerBase_le_one q)
  have := Real.log_nonneg hq
  have := mul_le_mul_of_nonneg_right (Nat.cast_div_le (α := ℝ) (m := n + 1) (n := r)) (sub_nonneg.2 (hD'.trans hU'))
  have := Real.log_nonneg one_le_two
  unfold windingLoopDensityLogRate windingLoopDensityLogSlope windingLoopDensityLogOffset
  push_cast at *
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (n + 1)), div_le_iff₀ (by positivity), Real.log_mul two_ne_zero (by positivity), show ∀ a b : ℝ, (a / (2 * r) + b / (2 * (n + 1))) * (2 * (n + 1)) = (n + 1) / r * a + b by intros; field_simp]
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

end

end PottsDiscontinuity.TorusLoops
