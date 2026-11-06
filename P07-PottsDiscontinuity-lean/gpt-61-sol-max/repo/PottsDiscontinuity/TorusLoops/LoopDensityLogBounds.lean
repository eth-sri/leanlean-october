module
public import Mathlib

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


open PottsDiscontinuity.TorusRC

variable {N : ℕ}

noncomputable section

/-- The expectation's logarithmic rate along positive even widths `M=2(n+1)`. -/
noncomputable def windingLoopDensityLogRate
    (hN : Even N) (hNp : 0 < N) (q : Set.Ici (1 : ℝ)) (n : ℕ) : ℝ := by
  let M := 2 * (n + 1)
  let hM : Even M := ⟨n + 1, by omega⟩
  
  exact Real.log (phi_T_windingLoopDensityExpectation hN hM hNp (by dsimp [M]; omega) q) / (M : ℝ)

/-- Constant contribution of the two finite factors in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogOffset (q : Set.Ici (1 : ℝ))  :=
  Real.log 2 + Real.log (2 * q.val)

/-- Coefficient of the truncated loop count in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogSlope (q : Set.Ici (1 : ℝ))  :=
  Real.log (windingLoopDensityUpperBase q) - Real.log (windingLoopDensityLowerBase q)

theorem windingLoopDensityLogOffset_nonneg (q : Set.Ici (1 : ℝ)) :
    0 ≤ windingLoopDensityLogOffset q := by
  have hq : (1 : ℝ) ≤ q.val := q.property
  
  
  exact add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by nlinarith))

theorem windingLoopDensityLogSlope_nonneg (q : Set.Ici (1 : ℝ)) :
    0 ≤ windingLoopDensityLogSlope q := by
  have hU  :=
    Real.log_nonneg (windingLoopDensityUpperBase_ge_one q)
  have hD  :=
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
  
  let M  := 2 * (n + 1)
  let hM : Even M := ⟨n + 1, by omega⟩
  let hMp : 0 < M := by  omega
  let m  := (n + 1) / r + 1
  let U  := windingLoopDensityUpperBase q
  let D  := windingLoopDensityLowerBase q
  let E  := phi_T_windingLoopDensityExpectation hN hM hNp hMp q
  let P  := phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m)
  let up  := Real.log 2 +  m  * Real.log U
  let low  :=  m  * Real.log D - Real.log (2 * q.val)
  have hqpos  := lt_of_lt_of_le zero_lt_one q.property
  have hU : 1 ≤ U := windingLoopDensityUpperBase_ge_one q
  
  have hDpos : 0 < D := windingLoopDensityLowerBase_pos q
  
  have htail := phi_T_windingLoopDensityWeightedTail_le_pow
    hN hNp q r (n + 1) hr hNle hthreshold harm
  
  
  have hPmul : P ≤ U ^ (N + 2 * (n + 1)) * P := by
    calc
      P = 1 * P := by ring
      _ ≤ U ^ (N + 2 * (n + 1)) * P :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hU) (torusRCProbability_nonneg hN hM q _)
  have hPsmall : P ≤ (1 / 16 ) ^ (n + 1) := by
    linarith
  have hPhalf : P ≤ 1 / 2 := by
    
    have hbase1 : (1 / 16 : ℝ) ≤ 1 := by norm_num
    
    exact hPsmall.trans (le_trans (by
                                     simpa using pow_le_pow_of_le_one (by norm_num) hbase1
                                       (show 1 ≤ n + 1 by omega)) (by norm_num))
  have hlowprob : 1 / 2 ≤ 1 - P := by linarith
  have htailUpper : U ^ (N + M) * P ≤ 1 := by
    
    
    have hpow : (1 / 16 : ℝ) ^ (n + 1) ≤ 1 := by
      bound
    grind
  have hEupper : E ≤ 2 * U ^ m := by
    have htrunc := phi_T_windingLoopDensityExpectation_le_tail hN hM hNp hMp q m
    
    have hUm : 1 ≤ U ^ m := one_le_pow₀ hU
    grind
  have hElower : D ^ m / (2 * q.val) ≤ E := by
    have htrunc := phi_T_windingLoopDensityExpectation_ge_tail hN hM hNp hMp q m
    
    have hcoef : 0 ≤ D ^ m / q.val := by
                                        bound
    have hrel : D ^ m / 2 / q.val ≤ D ^ m / q.val * (1 - P) := by
      have hmul := mul_le_mul_of_nonneg_left hlowprob hcoef
      grind
    have hden : D ^ m / 2 / q.val = D ^ m / (2 * q.val) := by ring
    rw [← hden]
    exact hrel.trans  htrunc 
  
  
  have hlogUp : Real.log E ≤ up := by
    have h := Real.log_le_log (phi_T_windingLoopDensityExpectation_pos hN hM hNp hMp q) hEupper
    
    rw [(by
           
           rw [Real.log_mul (by norm_num) (pow_ne_zero _ (lt_of_lt_of_le zero_lt_one hU).ne'), Real.log_pow] : Real.log (2 * U ^ m) = up)] at h
    exact h
  
  have hlogLow : low ≤ Real.log E := by
    have h := Real.log_le_log (by positivity) hElower
    
    rw [(by
           
           rw [Real.log_div (pow_ne_zero _ hDpos.ne') (by positivity), Real.log_pow] : Real.log (D ^ m / (2 * q.val)) = low)] at h
    exact h
  have hup0 : 0 ≤ up := by
    bound
  have hlow0 : low ≤ 0 := by
    dsimp [low]
    have hlogD  := Real.log_nonpos hDpos.le (windingLoopDensityLowerBase_le_one q)
    have hlogDen : 0 ≤ Real.log (2 * q.val) := by
      apply Real.log_nonneg
      grind
    nlinarith
  let C₀ := windingLoopDensityLogOffset q
  let C₁ := windingLoopDensityLogSlope q
  
  
  have hgap : up - low = C₀ +  m  * C₁ := by
    grind +locals
  
  
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hMp
  have hMcast :  M  = 2 * ((n + 1 : ℕ) : ℝ) := by
    simp [M]
  have hrateAbs :
      |Real.log E / (M )| ≤ (C₀ +  m  * C₁) /
        (2 *  (n + 1 : ℕ) ) := by
    calc
      |Real.log E / (M )| = |Real.log E| /  M  := by
        rw [abs_div, abs_of_pos hMR]
      _ ≤ (up - low) /  M  :=
        div_le_div_of_nonneg_right (by
                                      grind) hMR.le
      _ = (C₀ +  m  * C₁) /
          (2 *  (n + 1 : ℕ) ) := by rw [hgap, hMcast]
  
  
  
  have hquotMul :  ((n + 1) / r : ℕ)  *  r  ≤
      ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (n + 1) r
  have hmratio :  m  / (2 *  (n + 1 : ℕ) ) ≤
      1 / (2 *  r ) + 1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
    apply (div_le_iff₀ (by positivity)).2
    have hmcast :  m  = (((n + 1) / r : ℕ) : ℝ) + 1 := by simp [m]
    rw [hmcast]
    field_simp
    nlinarith [hquotMul]
  
  have hrate : |Real.log E / (M )| ≤
      C₁ / (2 *  r ) + (C₀ + C₁) /
        (2 *  (n + 1 ) ) := hrateAbs.trans (by
                                                     have hmul := mul_le_mul_of_nonneg_right hmratio (windingLoopDensityLogSlope_nonneg q)
                                                     grind)
  simpa [windingLoopDensityLogRate, M, E, hM, hMp, C₀, C₁] using hrate

end

end PottsDiscontinuity.TorusLoops
