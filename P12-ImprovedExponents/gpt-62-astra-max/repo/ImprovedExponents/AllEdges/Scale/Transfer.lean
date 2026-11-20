module
public import ImprovedExponents.AllEdges.Scale.Host
public import ThreeSumApsp.Util.Asymptotics.LogU

@[expose] public section
namespace ImprovedExponents.AllEdges.Scale
open Light Light.Sec3 ThreeSumApsp
/-- The number of levels is `O(log u)`: `⌊log₂ 3U⌋ + 1 ≤ 3 (1 + logU u)` for `1 ≤ U ≤ u`. -/
theorem aeLevels_le {U : ℕ} (hU : 1 ≤ U) {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (aeLevels U : ℝ) ≤ 3 * (1 + logU u) := by
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hhalf := Real.one_half_lt_log_two
  have h2u := log_two_le_logU u
  have hpow : 2 ^ Nat.log 2 (3 * U) ≤ 3 * U := Nat.pow_log_le_self 2 (by omega)
  -- ⌊log₂ 3U⌋ log 2 ≤ log 3U = log 3 + log U ≤ 2 log 2 + log U
  have hlog : (Nat.log 2 (3 * U) : ℝ) * Real.log 2 ≤ Real.log (3 * U) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_four]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hUu : Real.log U ≤ logU u := (Real.log_le_log (by positivity) hu).trans
    (log_le_logU (by linarith))
  simp only [aeLevels]
  push_cast
  rcases le_or_gt (Nat.log 2 (3 * U)) 1 with hL | hL
  · have : (Nat.log 2 (3 * U) : ℝ) ≤ 1 := by exact_mod_cast hL
    linarith
  · -- (⌊log₂ 3U⌋ − 2) / 2 ≤ (⌊log₂ 3U⌋ − 2) log 2 ≤ log U ≤ logU u
    have hL2 : (0 : ℝ) ≤ (Nat.log 2 (3 * U) : ℝ) - 2 := by
      have : (2 : ℝ) ≤ Nat.log 2 (3 * U) := by exact_mod_cast hL
      linarith
    have hleft := mul_le_mul_of_nonneg_left hhalf.le hL2
    linarith

/-- Two equality probes per level and linear work in the matrix area around each probe. -/
theorem solved {T : ℕ → ℝ → ℝ} (sol : SolvedIn aeTask T) :
    SolvedIn mpTask fun n u => 7000 * ((1 + logU u) * (T n (9*u) + (n:ℝ)^2)) := by
  apply host.solvedIn sol
  intro Tn hT n U u hn hU hu
  have ht := hT n (9*U) (9*u) hn (by omega) (by push_cast; linarith)
  have ht0 := (Nat.cast_nonneg _).trans ht
  have hn1 : (1:ℝ) ≤ (n:ℝ)^2 := by simp_all
  have hl : (aeLevels U:ℝ)+4 ≤ 7*(1+logU u) := by linarith [aeLevels_le hU hu, logU_pos u]
  have hc : 2*(Tn n (9*U):ℝ)+500*(n*n+1) ≤ 1000*(T n (9*u)+(n:ℝ)^2) := by nlinarith
  have h := mul_le_mul hl hc (by positivity) (by linarith [logU_pos u])
  simp only [time,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]; linarith

end ImprovedExponents.AllEdges.Scale
