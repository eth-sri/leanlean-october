module

public import ImprovedExponents.AllEdges.Scale.Transfer
public import ImprovedExponents.AllEdges.Model
public import ImprovedExponents.Pipeline.HostBound
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.TimeBound
public import ThreeSumApsp.Programs.Sec3.Corollary15_16.CountAndDetect
public import ThreeSumApsp.RunningTimes.FromClaims.Bounds
public import ThreeSumApsp.RunningTimes.Sec3.Theorem19.Layout
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ApspLayout
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.MinPlusLayout
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumLayout

@[expose] public section

/-! Transfer the all-edges bound to min-plus by prefix refinement, then to APSP
by repeated squaring.  Bound the product at every scaled polynomial weight
bound so that intermediate distances are covered by the same estimate. -/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.WordRam Filter

/-- A time bound of a solved task is nonnegative at sizes and bounds at least 1. -/
theorem _root_.Light.SolvedIn.nonneg {task} {T} (h : SolvedIn task T) {n}
    {u} (hn : 1 ≤ n) (hu : 1 ≤ u) : 0 ≤ T n u := by
  obtain ⟨_, _, Tn, _, -, -, hT⟩ := h
  exact (Nat.cast_nonneg (Tn n 1)).trans (hT n 1 u hn le_rfl (by grind))

/-- The bound of `ExplicitFrom` at the numbers `c n^κ`: for all large `n`,
`T(n, c n^κ) ≤ K (κ + 1) n^{3-δ} (log n)^e`. -/
theorem eventually_le_of_explicit {n₀} {K δ : ℝ} {e} {T : ℕ → ℝ → ℝ}
    (hb : ∀ (n : ℕ) (κ u : ℝ), n₀ ≤ n → 1 ≤ κ → u ≤ n ^ κ →
      T n u ≤ K * (κ * (n ^ (3 - δ) * Real.log n ^ e)))
    {c κ} (hκ : 0 ≤ κ) :
    ∀ᶠ n : ℕ in atTop,
      T n (c * n ^ κ) ≤ K * ((κ + 1) * (n ^ (3 - δ) * Real.log n ^ e)) := by
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop ⌈c⌉₊, eventually_ge_atTop 1] with n
    hn₀ hnc hn1
  refine hb n (κ + 1) _ hn₀ (by linarith) ?_
  have hcn : c ≤ n := by simp_all
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.rpow_add_one hn0, mul_comm]
  gcongr

/-- `⌈log₂ n⌉ + 1 ≤ 6 log n` for `n ≥ 2`. -/
theorem clog_add_one_le (n : ℕ) (hn : 2 ≤ n) : (Nat.clog 2 n) + 1 ≤ 6 * Real.log n := by
  have h : (Nat.clog 2 n) < Real.log n / Real.log 2 + 1 := by
    simpa [Real.logb] using Real.natCast_clog_lt_logb_add_one 2 n
  have hlog2 := Real.one_half_lt_log_two
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by simp_all)
  have hdiv : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The quadratic overhead of either reduction is within the target exponent. -/
private theorem quadratic {δ} (h : δ ≤ 1) :
    IsPowPolylog (fun n : ℕ => n ^ 2) (3 - δ) :=
  (isBigOPow_natCast_pow 2).isPowPolylog.mono (by grind)

/-- Bound the min-plus solver once, at **any** polynomial bound on the weights.
This includes the larger weights in every call from repeated squaring. -/
private theorem minPlusUniform {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (h : ExplicitFrom lightModelAE δ e) : ∃ T, SolvedIn mpTask T ∧ ∀ c κ : ℝ, 1 ≤ c → 0 ≤ κ →
      IsPowPolylog (fun n : ℕ => T n (c * n ^ κ)) (3 - δ) := by
  obtain ⟨_, K, T, hT, hb⟩ := h
  refine ⟨_, Scale.solved hT, fun c κ hc hκ => ?_⟩
  have hd : 1 ≤ 9*c := by linarith
  have ht : IsPowPolylog (fun n : ℕ => T n (9*c * (n : ℝ)^κ)) (3 - δ) := by
    apply (((isPowPolylog_rpow_mul_log_pow (3 - δ) e).const_mul (κ+1)).const_mul K).mono_left_of_nonneg
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact SolvedIn.nonneg hT hn (one_le_mul_of_one_le_of_one_le hd
        (Real.one_le_rpow (by simp_all) hκ))
    · exact eventually_le_of_explicit hb hκ
  have hl := (isPowPolylog_const 1).add (isPowPolylog_logU_mul_rpow hc hκ)
  simpa only [mul_assoc 9 c] using
    ((hl.mul (ht.add (quadratic hδ))).mono (b := 3-δ) (by simp)).const_mul 7000

/-- The two end statements that all-edges Exact Triangle with the saving `δ` gives: the
(min,+)-product and APSP in `O(n^a)` steps on the word RAM for every exponent `a > 3 - δ`. -/
structure MinPlusSolved (δ : ℝ) : Prop where
  /-- The (min,+)-product in `O(n^a)` steps for every `a > 3 - δ`. -/
  minPlus : ∀ a : ℝ, 3 - δ < a → SolvedInTime EndStatement.MinPlusProduct a 0
  /-- APSP in `O(n^a)` steps for every `a > 3 - δ`. -/
  apsp : ∀ a : ℝ, 3 - δ < a → SolvedInTime EndStatement.APSP a 0

/-- **From one all-edges solver to both end statements.** -/
theorem minPlusSolved_of_explicitFrom {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (h : ExplicitFrom lightModelAE δ e) : MinPlusSolved δ := by
  obtain ⟨T, hT, hpoly⟩ := minPlusUniform hδ h
  obtain ⟨c, C₀, hc, hs⟩ := claim_apspFromMinPlus
  constructor
  · intro a ha
    apply SolvedInPolylogTime.solvedInTime _ ha
    apply FromClaims.solvedInPolylogTime_of_claim realized_minPlusProduct
    exact fun κ hκ => ⟨_, hT, by simpa using (hpoly 1 κ le_rfl hκ).upperPowPolylog⟩
  · intro a ha
    apply SolvedInPolylogTime.solvedInTime _ ha
    apply FromClaims.solvedInPolylogTime_of_claim realized_apsp
    intro κ hκ
    refine ⟨_, hs T hT, IsPowPolylog.upperPowPolylog ?_⟩
    have h0 :=
      (isPowPolylog_log.const_mul 6).mono_left_of_nonneg (.of_forall fun _ => by grind)
        ((eventually_ge_atTop 2).mono clog_add_one_le)
    have hk : 0 ≤ κ + 1 := by linarith
    have hlog := (isPowPolylog_const 1).add (isPowPolylog_logU_mul_rpow hc hk)
    have hov := (((quadratic hδ).mul hlog).mono (b := 3-δ) (by simp)).const_mul C₀
    apply ((h0.mul ((hpoly c _ hc hk).add hov)).mono  (by simp)).congr
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [Real.rpow_add_one (by positivity : (n : ℝ) ≠ 0), mul_comm (n : ℝ)]

end ImprovedExponents.AllEdges
