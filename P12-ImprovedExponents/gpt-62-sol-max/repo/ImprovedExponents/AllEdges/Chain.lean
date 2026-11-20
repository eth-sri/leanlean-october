module

public import ImprovedExponents.AllEdges.Model
public import ImprovedExponents.Pipeline.HostBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import ThreeSumApsp.Machine.Solving
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.TimeBound
public import ImprovedExponents.AllEdges.MinPlus.Host
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.ApspLayout
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22.MinPlusLayout
public import ThreeSumApsp.RunningTimes.FromClaims.Bounds

@[expose] public section

/-! Prefix refinement and repeated squaring preserve the polynomial exponent of all-edges Exact Triangle, since they only add quadratic work and logarithmic factors. -/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.WordRam Filter

/-! ## The cost of prefix refinement -/

/-- The time of the (min,+)-product from all-edges Exact Triangle at time `T`. -/
noncomputable def mpBound (T : ℕ → ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  2000 * ((1 + logU u) * (T n (9 * u) + (n : ℝ) ^ 2))

private theorem mpTime_le {Tn : ℕ → ℕ → ℕ} {T : ℕ → ℝ → ℝ}
    (hT : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u)
    {n U : ℕ} {u : ℝ} (hn : 1 ≤ n) (hU : 1 ≤ U) (hu : (U : ℝ) ≤ u) :
    (MinPlus.Host.time Tn n U : ℝ) ≤ mpBound T n u := by
  have hb : (MinPlus.levels U : ℝ) ≤ 3 * (1 + logU u) := by
    have := log_mul_le_logU (by decide : (3 : ℕ) ≤ 4) hU hu
    simp [MinPlus.levels]
    linarith [logU_pos u]
  have hTn := hT n (9 * U) (9 * u) hn (by omega) (by push_cast; linarith)
  have hT0 : (0 : ℝ) ≤ T n (9 * u) := (Nat.cast_nonneg _).trans hTn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  have hL := logU_pos u
  have hround : 2 * (Tn n (9 * U) : ℝ) + 166 * (n : ℝ) ^ 2 + 232 ≤
      400 * (T n (9 * u) + (n : ℝ) ^ 2) := by linarith
  have hprod := mul_le_mul hb hround (by positivity) (by positivity)
  have hstart : (n : ℝ) ^ 2 ≤ (1 + logU u) * (T n (9 * u) + (n : ℝ) ^ 2) :=
    (le_add_of_nonneg_left hT0).trans (le_mul_of_one_le_left (by positivity) (by linarith))
  simp only [MinPlus.Host.time, MinPlus.Host.roundTime, MinPlus.Host.askTime, mpBound]
  push_cast
  nlinarith

/-- All-edges Exact Triangle gives a (min,+)-product at the same exponent, up to logarithms. -/
theorem solvedIn_mp_of_allEdges {T : ℕ → ℝ → ℝ} (h : SolvedIn aeTask T) :
    SolvedIn mpTask (mpBound T) :=
  MinPlus.Host.isHost.solvedIn h fun _ hTn _ _ _ hn hU hu => mpTime_le hTn hn hU hu

/-! ## Along bounds `u = n^κ` -/

/-- A time bound of a solved task is nonnegative at sizes and bounds at least 1. -/
theorem _root_.Light.SolvedIn.nonneg {task : Task} {T : ℕ → ℝ → ℝ} (h : SolvedIn task T) {n : ℕ}
    {u : ℝ} (hn : 1 ≤ n) (hu : 1 ≤ u) : 0 ≤ T n u := by
  obtain ⟨_, _, Tn, _, -, -, hT⟩ := h
  exact (Nat.cast_nonneg (Tn n 1)).trans (hT n 1 u hn le_rfl (by exact_mod_cast hu))

/-- `⌈log₂ n⌉ + 1 ≤ 6 log n` for `n ≥ 2`. -/
theorem clog_add_one_le (n : ℕ) (hn : 2 ≤ n) : (Nat.clog 2 n : ℝ) + 1 ≤ 6 * Real.log n := by
  have h : (Nat.clog 2 n : ℝ) < Real.log n / Real.log 2 + 1 := by
    simpa [Real.logb] using Real.natCast_clog_lt_logb_add_one 2 n
  have hlog2 := Real.one_half_lt_log_two
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hdiv : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

private theorem quadratic_polylog {δ : ℝ} (hδ : δ ≤ 1) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ 2) (3 - δ) :=
  (isBigOPow_natCast_pow 2).isPowPolylog.mono (by push_cast; linarith)

private theorem mul_polylog {f g : ℕ → ℝ} {a : ℝ}
    (hf : IsPowPolylog f 0) (hg : IsPowPolylog g a) :
    IsPowPolylog (fun n => f n * g n) a := by
  simpa using hf.mul hg

/-- The bit-search bound keeps its exponent along any polynomial bound on the entries.
This includes the enlarged bounds in APSP's repeated squaring. -/
private theorem mpBound_polylog {δ K : ℝ} {e n₀ : ℕ} (hδ : δ ≤ 1)
    {T : ℕ → ℝ → ℝ} (hs : SolvedIn mpTask (mpBound T))
    (hb : ExplicitBound δ e n₀ K T)
    {c κ : ℝ} {B : ℕ → ℝ} (hκ : 0 ≤ κ)
    (hB : ∀ n, 1 ≤ n → 1 ≤ B n ∧ B n ≤ c * (n : ℝ) ^ κ) :
    IsPowPolylog (fun n => mpBound T n (B n)) (3 - δ) := by
  have hL := (isPowPolylog_const 1).add (isPowPolylog_logU_of_le hB)
  obtain ⟨g, -, hg, he⟩ := (hb.along (c := 9 * c) (B := fun n => 9 * B n) hκ
    fun n hn => by nlinarith [(hB n hn).2]).exists_isPowPolylog
  refine ((mul_polylog hL (hg.add (quadratic_polylog hδ))).const_mul 2000).mono_left_of_nonneg ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn using hs.nonneg hn (hB n hn).1
  · filter_upwards [he] with n h
    have := logU_pos (B n)
    unfold mpBound
    gcongr

theorem minPlusInPolylog_of_explicitFrom
    {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ e) :
    Claim.MinPlusInPolylog lightModelAE (3 - δ) := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  intro κ hκ
  have hs := solvedIn_mp_of_allEdges hT
  exact ⟨_, hs, (mpBound_polylog hδ hs hb (c := 1) hκ fun _ hn =>
    ⟨Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ, (one_mul _).ge⟩).upperPowPolylog⟩

theorem apspInPolylog_of_explicitFrom
    {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ e) :
    Claim.ApspInPolylog lightModelAE (3 - δ) := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  intro κ hκ
  have hap := solvedIn_ap_of_mp (solvedIn_mp_of_allEdges hT)
  refine ⟨_, hap, ?_⟩
  let B (n : ℕ) := 16 * ((n : ℝ) ^ 2 * (n : ℝ) ^ κ)
  have hB n (hn : 1 ≤ n) : 1 ≤ B n ∧ B n ≤ 16 * (n : ℝ) ^ (κ + 2) := by
    have hn' := (Nat.one_le_cast (α := ℝ)).2 hn
    refine ⟨one_le_mul_of_one_le_of_one_le (by norm_num)
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn') (Real.one_le_rpow hn' hκ)), ?_⟩
    dsimp only [B]
    rw [Real.rpow_add (by positivity), Real.rpow_ofNat, mul_comm ((n : ℝ) ^ κ)]
  have hmp := mpBound_polylog hδ (solvedIn_mp_of_allEdges hT) hb (by linarith : 0 ≤ κ + 2) hB
  have hsum := hmp.add ((quadratic_polylog hδ).const_mul 200)
  refine (mul_polylog (isPowPolylog_log.const_mul 6) hsum).upperPowPolylog.mono_left ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hpos := (solvedIn_mp_of_allEdges hT).nonneg (n := n) (by omega) (hB n (by omega)).1
  exact mul_le_mul_of_nonneg_right (clog_add_one_le n hn) (by positivity)

/-! ## The end statements -/

/-- **The (min,+)-product in time `O(n^{3-δ} (log n)^{O(1)})` on the word RAM**, from all-edges
Exact Triangle in time `n^{3-δ} (log n)^e`. -/
theorem minPlus_polylog_of_explicitFrom
    {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ e) :
    SolvedInPolylogTime EndStatement.MinPlusProduct (3 - δ) :=
  FromClaims.solvedInPolylogTime_of_claim (fun T hT => realized_minPlusProduct T hT)
    (minPlusInPolylog_of_explicitFrom hδ h)

/-- **APSP in time `O(n^{3-δ} (log n)^{O(1)})` on the word RAM**, from all-edges Exact Triangle in
time `n^{3-δ} (log n)^e`. -/
theorem apsp_polylog_of_explicitFrom
    {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ e) :
    SolvedInPolylogTime EndStatement.APSP (3 - δ) :=
  FromClaims.solvedInPolylogTime_of_claim (fun T hT => realized_apsp T hT)
    (apspInPolylog_of_explicitFrom hδ h)

/-- The two end statements that all-edges Exact Triangle with the saving `δ` gives: the
(min,+)-product and APSP in `O(n^a)` steps on the word RAM for every exponent `a > 3 - δ`. -/
structure MinPlusSolved (δ : ℝ) : Prop where
  /-- The (min,+)-product in `O(n^a)` steps for every `a > 3 - δ`. -/
  minPlus : ∀ a : ℝ, 3 - δ < a → SolvedInTime EndStatement.MinPlusProduct a 0
  /-- APSP in `O(n^a)` steps for every `a > 3 - δ`. -/
  apsp : ∀ a : ℝ, 3 - δ < a → SolvedInTime EndStatement.APSP a 0

/-- **From all-edges Exact Triangle in time `n^{3-δ} (log n)^e` to the end statements.** -/
theorem minPlusSolved_of_explicitFrom
    {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ e) : MinPlusSolved δ :=
  ⟨fun _ ha => (minPlus_polylog_of_explicitFrom hδ h).solvedInTime ha,
    fun _ ha => (apsp_polylog_of_explicitFrom hδ h).solvedInTime ha⟩

end ImprovedExponents.AllEdges
