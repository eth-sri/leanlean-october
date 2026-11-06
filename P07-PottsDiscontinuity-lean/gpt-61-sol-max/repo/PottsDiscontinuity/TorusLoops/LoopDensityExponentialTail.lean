module
public import Mathlib

public import PottsDiscontinuity.TorusLoops.LoopDensityObservable
public import PottsDiscontinuity.TorusLoops.LoopTailProbability

/-!
# Exponential control of the weighted large-loop tail

For a threshold proportional to the width, a sufficiently small one-arm
probability makes both the large-loop probability and its maximal observable
contribution exponentially small in the width.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops


open PottsDiscontinuity.TorusRC

variable {N : ℕ}

noncomputable section

/-- Amplification factor combining the maximal observable with the seam cost. -/
noncomputable def windingLoopTailAmplification (q : Set.Ici (1 : ℝ)) : ℝ :=
  2 * windingLoopDensityUpperBase q /
    (1 - (rcCriticalParameter q).val)

/-- A one-arm probability threshold that absorbs the seam and observable
amplification for a loop threshold of scale `n / r`. -/
noncomputable def windingLoopTailArmThreshold (q : Set.Ici (1 : ℝ)) (r : ℕ) : ℝ :=
  (1 / (16 * windingLoopTailAmplification q ^ 4)) ^ (3 * r)

theorem windingLoopTailAmplification_ge_one (q : Set.Ici (1 : ℝ)) :
    1 ≤ windingLoopTailAmplification q := by
  have hU  := windingLoopDensityUpperBase_ge_one q
  
  have ha_le : 1 - (rcCriticalParameter q).val ≤ 1 := by
    linarith [criticalParameter_pos q]
  
  apply (le_div_iff₀ (sub_pos.mpr (criticalParameter_lt_one q))).2
  nlinarith

theorem windingLoopTailArmThreshold_pos (q : Set.Ici (1 : ℝ)) (r : ℕ) :
    0 < windingLoopTailArmThreshold q r := by
  have hB  :=
    lt_of_lt_of_le zero_lt_one (windingLoopTailAmplification_ge_one q)
  unfold windingLoopTailArmThreshold
  positivity

/-- At width `2*n`, with threshold `n/r+1`, the maximal observable times the
large-loop probability is at most `16^{-n}` when the one-arm input is small
enough. -/
theorem phi_T_windingLoopDensityWeightedTail_le_pow
    (hN : Even N) (hNp : 0 < N) (q : Set.Ici (1 : ℝ))
    (r n : ℕ) (hr : 0 < r) (hNle : N ≤ 2 * n)
    (hthreshold : 9 * N ≤ n / r + 1)
    (harm : rectangleFreeOneArmProbability q (N / 2 - 1) ≤
      windingLoopTailArmThreshold q r) :
    windingLoopDensityUpperBase q ^ (N + 2 * n) *
      phi_T_probability hN  ⟨n, by omega⟩  q
        (windingLoopTailEvent hN (show Even (2 * n) from ⟨n, by omega⟩)
          hNp (by omega) (n / r + 1)) ≤
      (1 / 16 : ℝ) ^ n := by
  
  let M  := 2 * n
  let hM : Even M := by
                       grind
  let hMp : 0 < M := by  omega
  let m  := n / r + 1
  let U  := windingLoopDensityUpperBase q
  let B  := windingLoopTailAmplification q
  let θ  := 1 / (16 * B ^ 4)
  let ρ  := rectangleFreeOneArmProbability q (N / 2 - 1)
  let k  := (m - 3 * N + 1) / 2
  
  have hU0 : 0 ≤ U := le_trans (by norm_num) (windingLoopDensityUpperBase_ge_one q)
  have hB : 1 ≤ B := windingLoopTailAmplification_ge_one q
  have hB0 : 0 ≤ B := by
                        nlinarith
  have hθ0 : 0 < θ := by
    
    positivity
  have hθ1 : θ ≤ 1 := by
    bound
  have hρ0 : 0 ≤ ρ := by
    change 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1)
    unfold rectangleFreeOneArmProbability
    exact NNReal.coe_nonneg _
  
  
  have hklarge : m ≤ 3 * k := by
    omega
  
  have hρpow : ρ ^ k ≤ θ ^ n := by
    calc
      ρ ^ k ≤ (θ ^ (3 * r)) ^ k :=
        pow_le_pow_left₀ hρ0  harm  k
      _ = θ ^ (3 * r * k) := by rw [← pow_mul]
      _ ≤ θ ^ (r * m) := by
        apply pow_le_pow_of_le_one hθ0.le hθ1
        nlinarith 
      _ ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1 (by
                                                      
                                                      
                                                      calc
                                                        n = n % r + r * (n / r) := (Nat.mod_add_div n r).symm
                                                        _ ≤ r + r * (n / r) := Nat.add_le_add_right (Nat.mod_lt n hr).le _
                                                        _ = r * (n / r + 1) := by rw [Nat.mul_add]; omega)
  
  have ha  := sub_pos.mpr (criticalParameter_lt_one q)
   
  have hpow2 : (2 : ℝ) ^ M ≤ 2 ^ (N + M) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  
  have hweighted : U ^ (N + M) *
      phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
        B ^ (N + M) * ρ ^ k := by
    
    have htail' := mul_le_mul_of_nonneg_left (torusRCProbability_windingTail_le_rootUnion
                                                hN hM hNp hMp q m) (pow_nonneg hU0 (N + M))
    calc
      _ ≤ U ^ (N + M) *
          ( 2  ^ M * ρ ^ k /
            (1 - (rcCriticalParameter q).val) ^ (N + M)) := htail'
      _ =  U ^ (N + M) *
          (2 ^ M / (1 - (rcCriticalParameter q).val) ^ (N + M))  * ρ ^ k := by ring
      _ ≤ B ^ (N + M) * ρ ^ k :=
        mul_le_mul_of_nonneg_right (by
                                      
                                      
                                      
                                      
                                      calc
                                        U ^ (N + M) *
                                            (2 ^ M / (1 - (rcCriticalParameter q).val) ^ (N + M)) ≤
                                           U ^ (N + M) * 2 ^ (N + M)  /
                                            (1 - (rcCriticalParameter q).val) ^ (N + M) := by
                                              calc
                                                _ =  U ^ (N + M) * 2 ^ M  /
                                                    (1 - (rcCriticalParameter q).val) ^ (N + M) := by ring
                                                _ ≤  U ^ (N + M) * 2 ^ (N + M)  /
                                                    (1 - (rcCriticalParameter q).val) ^ (N + M) :=
                                                  div_le_div_of_nonneg_right (by
                                                                                  bound) (pow_pos ha _).le
                                        _ = B ^ (N + M) := (by
                                                              dsimp [B, windingLoopTailAmplification]
                                                              
                                                              ring)) (pow_nonneg hρ0 _)
  have hsmall : B ^ (N + M) * ρ ^ k ≤ (1 / 16 ) ^ n := by
    
    calc
      B ^ (N + 2 * n) * ρ ^ k ≤ B ^ (N + 2 * n) * θ ^ n :=
        mul_le_mul_of_nonneg_left hρpow (pow_nonneg hB0 _)
      _ = B ^ N * (B ^ 2 * θ) ^ n := by
        
        ring
      _ ≤ (1 / 16 ) ^ n := by
        have hBpowN : B ^ N ≤ B ^ (2 * n) := by
                                               bound
        
        
        exact (mul_le_mul_of_nonneg_right hBpowN (pow_nonneg (mul_nonneg (pow_nonneg hB0 _) hθ0.le) _)).trans_eq (by
                                rw [show B ^ (2 * n) = (B ^ 2) ^ n by rw [pow_mul]]
                                rw [← mul_pow]
                                
                                dsimp [θ]
                                field_simp)
  
  simpa [M, m, hN, hM, hMp, U, B] using  hweighted.trans hsmall 

end

end PottsDiscontinuity.TorusLoops
