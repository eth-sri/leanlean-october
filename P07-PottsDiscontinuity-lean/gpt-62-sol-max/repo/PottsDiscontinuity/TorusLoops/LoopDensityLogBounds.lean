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
  let hM : Even M := ⟨n + 1, by omega⟩
  let hMp : 0 < M := by omega
  exact Real.log (phi_T_windingLoopDensityExpectation hN hM hNp hMp q) / (M : ℝ)

/-- Constant contribution of the two finite factors in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogOffset (q : Set.Ici (1 : ℝ)) : ℝ :=
  Real.log 2 + Real.log (2 * q.val)

/-- Coefficient of the truncated loop count in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogSlope (q : Set.Ici (1 : ℝ)) : ℝ :=
  Real.log (windingLoopDensityUpperBase q) - Real.log (windingLoopDensityLowerBase q)

theorem windingLoopDensityLogSlope_nonneg (q : Set.Ici (1 : ℝ)) :
    0 ≤ windingLoopDensityLogSlope q := by
  have hU : 0 ≤ Real.log (windingLoopDensityUpperBase q) :=
    Real.log_nonneg (windingLoopDensityUpperBase_ge_one q)
  have hD : Real.log (windingLoopDensityLowerBase q) ≤ 0 :=
    Real.log_nonpos (windingLoopDensityLowerBase_pos q).le
      (windingLoopDensityLowerBase_le_one q)
  unfold windingLoopDensityLogSlope
  linarith

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
  classical
  let M : ℕ := 2 * (n + 1)
  let hM : Even M := ⟨n + 1, by omega⟩
  let hMp : 0 < M := by omega
  let m : ℕ := (n + 1) / r + 1
  let U : ℝ := windingLoopDensityUpperBase q
  let D : ℝ := windingLoopDensityLowerBase q
  let E : ℝ := phi_T_windingLoopDensityExpectation hN hM hNp hMp q
  let P : ℝ := phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m)
  have hq : (1 : ℝ) ≤ q.val := q.property
  have hqpos := zero_lt_one.trans_le hq
  have hU : 1 ≤ U := windingLoopDensityUpperBase_ge_one q
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hDpos : 0 < D := windingLoopDensityLowerBase_pos q
  have htail : U ^ (N + M) * P ≤ (1 / 16 : ℝ) ^ (n + 1) :=
    phi_T_windingLoopDensityWeightedTail_le_pow hN hNp q r (n + 1) hr hNle hthreshold harm
  have hsmall : U ^ (N + M) * P ≤ 1 / 16 := htail.trans (by
    simpa using pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 16 : ℝ)) (by norm_num) (show 1 ≤ n + 1 by omega))
  have hP := (le_mul_of_one_le_left (torusRCProbability_nonneg hN hM q _)
    (one_le_pow₀ (n := N + M) hU)).trans hsmall
  have hu : E ≤ 2 * U ^ m :=
    (phi_T_windingLoopDensityExpectation_le_tail hN hM hNp hMp q m).trans
      (by linarith [one_le_pow₀ (n := m) hU])
  have hd : D ^ m / (2 * q.val) ≤ E := by
    refine le_trans ?_ (phi_T_windingLoopDensityExpectation_ge_tail hN hM hNp hMp q m)
    rw [mul_comm 2 q.val, ← div_div, div_eq_mul_inv (D ^ m / q.val) 2]
    exact mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ)⁻¹ ≤ 1 - P) (by positivity)
  have hlu := Real.log_le_log (phi_T_windingLoopDensityExpectation_pos hN hM hNp hMp q) hu
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hUpos.ne'), Real.log_pow] at hlu
  have hld := Real.log_le_log (by positivity : 0 < D ^ m / (2 * q.val)) hd
  rw [Real.log_div (pow_ne_zero _ hDpos.ne') (by positivity), Real.log_pow] at hld
  let A := windingLoopDensityLogOffset q
  let B := windingLoopDensityLogSlope q
  have hlog : |Real.log E| ≤ A + (m : ℝ) * B := by
    change |Real.log E| ≤ Real.log 2 + Real.log (2 * q.val) + (m : ℝ) * (Real.log U - Real.log D)
    rw [abs_le]
    constructor <;> nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num),
      Real.log_nonneg (show (1 : ℝ) ≤ 2 * q.val by linarith only [hq]),
      mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg hU),
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m)
        (Real.log_nonpos hDpos.le (windingLoopDensityLowerBase_le_one q))]
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hMp
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hm : (m : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / r + 1 := by
    rw [show (m : ℝ) = ((n + 1) / r : ℕ) + 1 by simp [m], add_le_add_iff_right, le_div_iff₀ hrR]
    exact_mod_cast Nat.div_mul_le_self (n + 1) r
  change |Real.log E / M| ≤ _
  rw [abs_div, abs_of_pos hMR]
  apply (div_le_div_of_nonneg_right hlog hMR.le).trans
  calc
    _ ≤ (A + ((((n + 1 : ℕ) : ℝ) / r) + 1) * B) / M := by
      gcongr
      exact windingLoopDensityLogSlope_nonneg q
    _ = _ := by
      change _ = B / _ + (A + B) / _
      dsimp only [M]
      push_cast
      field_simp
      <;> ring

end

end PottsDiscontinuity.TorusLoops
