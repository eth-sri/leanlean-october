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
  let hMp : 0 < M := by dsimp [M]; omega
  exact Real.log (phi_T_windingLoopDensityExpectation hN hM hNp hMp q) / (M : ℝ)

/-- Constant contribution of the two finite factors in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogOffset (q : Set.Ici (1 : ℝ)) : ℝ :=
  Real.log 2 + Real.log (2 * q.val)

/-- Coefficient of the truncated loop count in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogSlope (q : Set.Ici (1 : ℝ)) : ℝ :=
  Real.log (windingLoopDensityUpperBase q) - Real.log (windingLoopDensityLowerBase q)

theorem windingLoopDensityLogOffset_nonneg (q : Set.Ici (1 : ℝ)) :
    0 ≤ windingLoopDensityLogOffset q :=
  add_nonneg (Real.log_nonneg (by norm_num))
    (Real.log_nonneg (by linarith [Set.mem_Ici.mp q.property]))

theorem windingLoopDensityLogSlope_nonneg (q : Set.Ici (1 : ℝ)) :
    0 ≤ windingLoopDensityLogSlope q :=
  sub_nonneg_of_le <| (Real.log_nonpos (windingLoopDensityLowerBase_pos q).le
    (windingLoopDensityLowerBase_le_one q)).trans
    (Real.log_nonneg (windingLoopDensityUpperBase_ge_one q))

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
  let hMp : 0 < M := by dsimp [M]; omega
  let m : ℕ := (n + 1) / r + 1
  let U : ℝ := windingLoopDensityUpperBase q
  let D : ℝ := windingLoopDensityLowerBase q
  let E : ℝ := phi_T_windingLoopDensityExpectation hN hM hNp hMp q
  let P : ℝ := phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m)
  let up : ℝ := Real.log 2 + (m : ℝ) * Real.log U
  let low : ℝ := (m : ℝ) * Real.log D - Real.log (2 * q.val)
  have hqpos : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  have hU : 1 ≤ U := windingLoopDensityUpperBase_ge_one q
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hDpos : 0 < D := windingLoopDensityLowerBase_pos q
  have hDle : D ≤ 1 := windingLoopDensityLowerBase_le_one q
  have htail : U ^ (N + M) * P ≤ (1 / 16 : ℝ) ^ (n + 1) :=
    phi_T_windingLoopDensityWeightedTail_le_pow hN hNp q r (n + 1) hr hNle hthreshold harm
  have hPnonneg : 0 ≤ P := torusRCProbability_nonneg hN hM q _
  have hPsmall : P ≤ (1 / 16 : ℝ) ^ (n + 1) :=
    (le_mul_of_one_le_left hPnonneg (one_le_pow₀ hU : 1 ≤ U ^ (N + M))).trans htail
  have hPhalf : P ≤ 1 / 2 :=
    hPsmall.trans <| (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num) (show 1 ≤ n + 1 by omega)).trans (by norm_num)
  have htailUpper : U ^ (N + M) * P ≤ 1 :=
    htail.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hEupper : E ≤ 2 * U ^ m := by
    have htrunc : E ≤ U ^ m + U ^ (N + M) * P :=
      phi_T_windingLoopDensityExpectation_le_tail hN hM hNp hMp q m
    have hUm : 1 ≤ U ^ m := one_le_pow₀ hU
    linarith
  have hElower : D ^ m / (2 * q.val) ≤ E := by
    have htrunc : D ^ m / q.val * (1 - P) ≤ E :=
      phi_T_windingLoopDensityExpectation_ge_tail hN hM hNp hMp q m
    have hcoef : 0 ≤ D ^ m / q.val := div_nonneg (pow_nonneg hDpos.le _) hqpos.le
    have hmul := mul_le_mul_of_nonneg_left (by linarith : (1 / 2 : ℝ) ≤ 1 - P) hcoef
    linarith [show D ^ m / (2 * q.val) = D ^ m / q.val * (1 / 2 : ℝ) by ring]
  have hEpos : 0 < E := phi_T_windingLoopDensityExpectation_pos hN hM hNp hMp q
  have hlogUp : Real.log E ≤ up := by
    simpa [up, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero m hUpos.ne'), Real.log_pow]
      using Real.log_le_log hEpos hEupper
  have hlogLow : low ≤ Real.log E := by
    simpa [low, Real.log_div (pow_ne_zero m hDpos.ne') (by positivity : 2 * q.val ≠ 0), Real.log_pow]
      using Real.log_le_log (by positivity) hElower
  have hup0 : 0 ≤ up :=
    add_nonneg (Real.log_nonneg (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hU))
  have hlow0 : low ≤ 0 := by
    have hlogD : Real.log D ≤ 0 := Real.log_nonpos hDpos.le hDle
    have hlogDen : 0 ≤ Real.log (2 * q.val) := Real.log_nonneg (by linarith [Set.mem_Ici.mp q.property])
    dsimp [low]; nlinarith
  let C₀ := windingLoopDensityLogOffset q
  let C₁ := windingLoopDensityLogSlope q
  have hC₁ : 0 ≤ C₁ := windingLoopDensityLogSlope_nonneg q
  have hgap : up - low = C₀ + (m : ℝ) * C₁ := by
    dsimp [up, low, C₀, C₁, windingLoopDensityLogOffset, windingLoopDensityLogSlope, U, D]; ring
  have habs : |Real.log E| ≤ up - low :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hMp
  have hrateAbs : |Real.log E / (M : ℝ)| ≤ (C₀ + (m : ℝ) * C₁) / (2 * ((n + 1 : ℕ) : ℝ)) := by
    rw [abs_div, abs_of_pos hMR, ← hgap, show (2 * ((n + 1 : ℕ) : ℝ)) = (M : ℝ) by simp [M]]
    exact div_le_div_of_nonneg_right habs hMR.le
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hquotMul : (((n + 1) / r : ℕ) : ℝ) * (r : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (n + 1) r
  have hmratio : (m : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) ≤
      1 / (2 * (r : ℝ)) + 1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
    rw [div_le_iff₀ (by positivity), show (m : ℝ) = (((n + 1) / r : ℕ) : ℝ) + 1 by simp [m]]
    field_simp; nlinarith [hquotMul]
  have hmul := mul_le_mul_of_nonneg_right hmratio hC₁
  have hfinish : (C₀ + (m : ℝ) * C₁) / (2 * ((n + 1 : ℕ) : ℝ)) ≤
      C₁ / (2 * (r : ℝ)) + (C₀ + C₁) / (2 * ((n + 1 : ℕ) : ℝ)) := by
    linarith [show (C₀ + (m : ℝ) * C₁) / (2 * ((n + 1 : ℕ) : ℝ)) =
        C₀ / (2 * ((n + 1 : ℕ) : ℝ)) + ((m : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) * C₁ by ring,
      show C₀ / (2 * ((n + 1 : ℕ) : ℝ)) + (1 / (2 * (r : ℝ)) + 1 / (2 * ((n + 1 : ℕ) : ℝ))) * C₁ =
        C₁ / (2 * (r : ℝ)) + (C₀ + C₁) / (2 * ((n + 1 : ℕ) : ℝ)) by ring]
  simpa [windingLoopDensityLogRate, M, E, hM, hMp, C₀, C₁] using hrateAbs.trans hfinish

end

end PottsDiscontinuity.TorusLoops
