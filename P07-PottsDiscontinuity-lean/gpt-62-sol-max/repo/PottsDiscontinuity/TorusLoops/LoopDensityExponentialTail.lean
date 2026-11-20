module

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

open PottsDiscontinuity.Torus
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
  have hU := windingLoopDensityUpperBase_ge_one q
  have ha := sub_pos.mpr (criticalParameter_lt_one q)
  have ha_le : 1 - (rcCriticalParameter q).val ≤ 1 := by
    linarith [criticalParameter_pos q]
  unfold windingLoopTailAmplification
  apply (le_div_iff₀ ha).2
  nlinarith

theorem windingLoopTailArmThreshold_pos (q : Set.Ici (1 : ℝ)) (r : ℕ) :
    0 < windingLoopTailArmThreshold q r := by
  have hB :=
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
      phi_T_probability hN (show Even (2 * n) from ⟨n, by omega⟩) q
        (windingLoopTailEvent hN (show Even (2 * n) from ⟨n, by omega⟩)
          hNp (by omega) (n / r + 1)) ≤
      (1 / 16 : ℝ) ^ n := by
  classical
  let M : ℕ := 2 * n
  let hM : Even M := ⟨n, by omega⟩
  let hMp : 0 < M := by omega
  let m : ℕ := n / r + 1
  let U : ℝ := windingLoopDensityUpperBase q
  let B : ℝ := windingLoopTailAmplification q
  let θ : ℝ := 1 / (16 * B ^ 4)
  let ρ : ℝ := rectangleFreeOneArmProbability q (N / 2 - 1)
  let k : ℕ := (m - 3 * N + 1) / 2
  have hU := windingLoopDensityUpperBase_ge_one q
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hB : 1 ≤ B := windingLoopTailAmplification_ge_one q
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by bound
  have hρ0 : 0 ≤ ρ := by
    change 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1)
    unfold rectangleFreeOneArmProbability
    exact NNReal.coe_nonneg _
  have hklarge : m ≤ 3 * k := by omega
  have hnr : n ≤ r * m := by
    dsimp [m]
    rw [Nat.mul_add, Nat.mul_one]
    linarith [Nat.mod_add_div n r, Nat.mod_lt n hr]
  have hρpow : ρ ^ k ≤ θ ^ n := by
    refine (pow_le_pow_left₀ hρ0 harm k).trans ?_
    change (θ ^ (3 * r)) ^ k ≤ _
    rw [← pow_mul]
    apply pow_le_pow_of_le_one hθ0.le hθ1
    nlinarith [Nat.mul_le_mul_left r hklarge]
  let d := 1 - (rcCriticalParameter q).val
  have hd : 0 < d := sub_pos.mpr (criticalParameter_lt_one q)
  have htail := torusRCProbability_windingTail_le_rootUnion hN hM hNp hMp q m
  calc
    _ ≤ U ^ (N + M) * (2 ^ M * ρ ^ k / d ^ (N + M)) :=
      mul_le_mul_of_nonneg_left htail (pow_nonneg hU0 _)
    _ = (2 ^ M * (U ^ (N + M) / d ^ (N + M))) * ρ ^ k := by ring
    _ ≤ B ^ (N + M) * ρ ^ k := by
      change _ ≤ ((2 * U) / d) ^ (N + M) * ρ ^ k
      rw [div_pow, mul_pow, ← mul_div_assoc]
      gcongr <;> norm_num
    _ ≤ B ^ (4 * n) * θ ^ n := mul_le_mul
      (pow_le_pow_right₀ hB (by omega)) hρpow (pow_nonneg hρ0 _) (pow_nonneg hB0 _)
    _ = _ := by
      rw [pow_mul, ← mul_pow]
      congr 1
      dsimp [θ]
      field_simp

end

end PottsDiscontinuity.TorusLoops
