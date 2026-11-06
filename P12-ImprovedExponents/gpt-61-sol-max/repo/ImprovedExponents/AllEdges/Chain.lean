module

public import Mathlib.Tactic
public import ImprovedExponents.AllEdges.Model
public import ImprovedExponents.Pipeline.HostBound
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22

@[expose] public section

/-!
# From all-edges Exact Triangle to the (min,+)-product and APSP

Footnote 10 of the paper: the (min,+)-product reduces to all-edges Exact Triangle "on the same `n`
vertices", so APSP keeps all of the saving of Exact Triangle rather than a third. The chain is

  all-edges Exact Triangle → all pairs (`pairsTask`) → (min,+)-product (`mpTask`) → APSP (`apTask`),

where the first step is our host (`ImprovedExponents.AllEdges.Pairs`, delivered here as the
hypothesis `PairsFromAllEdges`), and the last two are upstream's (`isHost_mp`, the bit search of
[VW18, Theorem 4.2], and `claim_apspFromMinPlus`, repeated squaring).  This file does the
arithmetic of the running times along bounds `u = n^κ` on the numbers:

* `solvedIn_mp_of_allEdges`: the (min,+)-product in time `O(log² u · (T(n, 54 u) + n²))` from
  all-edges Exact Triangle in time `T`;
* `minPlusInPolylog_of_explicitFrom`, `apspInPolylog_of_explicitFrom`: from all-edges Exact
  Triangle in time `n^{3-δ} (log n)^e` (`ExplicitFrom lightModelAE δ e`), the (min,+)-product and
  APSP in time `O(n^{3-δ} (log n)^{O(1)})`;
* `MinPlusSolved δ` and `minPlusSolved_of_explicitFrom`: the two end statements of the word RAM for
  every exponent above `3 - δ`.
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.WordRam Filter

/-! ## All pairs and the (min,+)-product -/

/-- **The transfer from all-edges Exact Triangle to all pairs** that the host
`ImprovedExponents.AllEdges.Pairs` delivers, with its constant `CA`: a solver of all-edges Exact
Triangle in time `T` gives a solver of `pairsTask` in time `CA (1 + log u) (T(n, 9u) + n²)`. -/
def PairsFromAllEdges (CA : ℝ) : Prop :=
  ∀ T , SolvedIn aeTask T →
    SolvedIn pairsTask fun n u => CA * ((1 + logU u) * (T n (9 * u) + n ^ 2))

/-- The time of upstream's bit search for the (min,+)-product (`mpTime`: `mpRounds U` calls of the
pairs solver at the bound `6U`, each with `O(n²)` more steps), against a real bound `Tp` on the
pairs solver: at most `1100 log u (Tp(n, 6u) + n²)`. -/
theorem mpTime_le {Tn} {Tp : ℕ → ℝ → ℝ}
    (hTn : ∀ (n U : ℕ) u, 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ Tp n u)
    {n U : ℕ} {u} (hn : 1 ≤ n) (hU : 1 ≤ U) (hu : (U : ℝ) ≤ u) :
    (mpTime Tn n U : ℝ) ≤ 1100 * (logU u * (Tp n (6 * u) + (n : ℝ) ^ 2)) := by
  have hR := MinPlusFromNeg.mpRounds_le hU hu
  have  := Real.one_half_lt_log_two.trans_le (log_two_le_logU u)
  have hT := hTn n (6 * U) (6 * u) hn (by omega) (by push_cast; linarith)

  have  : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (mod_cast hn)
  have hL0 : (0 : ℝ) ≤ logU u := by linarith
  have hstep :=
    mul_le_mul hR (by linarith) (by positivity) (by positivity)

  have hb : (n : ℝ) ^ 2 ≤ 2 * logU u * (n : ℝ) ^ 2 :=
    le_mul_of_one_le_left (by positivity) (by linarith)

  have hsq := (sq (n : ℝ)).symm
  simp only [mpTime]
  push_cast
  rw [hsq]
  nlinarith [hstep, mul_nonneg hL0 (by linarith), hb, mul_nonneg hL0 ((Nat.cast_nonneg _).trans hT)]

/-- **The (min,+)-product from all-edges Exact Triangle**: upstream's bit search over our host. -/
def solvedIn_mp_of_allEdges {CA} (hp : PairsFromAllEdges CA) {T}
     h :=
  isHost_mp.solvedIn (hp T h) fun _ hTn _ _ _ hn hU hu => mpTime_le hTn hn hU hu

/-! ## Along bounds `u = n^κ` -/

/-- A time bound of a solved task is nonnegative at sizes and bounds at least 1. -/
theorem _root_.Light.SolvedIn.nonneg {task : Task} {T : ℕ → ℝ → ℝ} (h : SolvedIn task T) {n : ℕ}
    {u : ℝ} (hn : 1 ≤ n) (hu : 1 ≤ u) : 0 ≤ T n u := by
  obtain ⟨_, _, Tn, _, -, -, hT⟩ := h
  exact (Nat.cast_nonneg (Tn n 1)).trans (hT n 1 u hn le_rfl (mod_cast hu))

/-- The bound of `ExplicitFrom` at the numbers `c n^κ`: for all large `n`,
`T(n, c n^κ) ≤ K (κ + 1) n^{3-δ} (log n)^e`. -/
theorem eventually_le_of_explicit {n₀} {K δ : ℝ} {e} {T : ℕ → ℝ → ℝ}
    (hb : ∀ (n : ℕ) (κ u ), n₀ ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)))
    {c κ} (hκ : 0 ≤ κ) :
    ∀ᶠ n : ℕ in atTop,
      T n (c * n ^ κ) ≤ K * ((κ + 1) * (n ^ (3 - δ) * Real.log n ^ e)) := by
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop ⌈c⌉₊, eventually_ge_atTop 1] with n
    hn₀ hnc hn1
  refine hb n (κ + 1) _ hn₀ (by linarith) ?_
  have  : c ≤ (n : ℝ) := (Nat.le_ceil c).trans (mod_cast hnc)
  have  : (n : ℝ) ≠ 0 := by positivity
  grind [Real.rpow_add_one, mul_comm, mul_le_mul_of_nonneg_left, Real.rpow_nonneg]

/-- `⌈log₂ n⌉ + 1 ≤ 6 log n` for `n ≥ 2`. -/
theorem clog_add_one_le n (hn : 2 ≤ n) : (Nat.clog 2 n : ℝ) + 1 ≤ 6 * Real.log n := by
  have  := by
    simpa [Real.logb] using Real.natCast_clog_lt_logb_add_one 2 n
  have  := Real.one_half_lt_log_two
  have  : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (mod_cast hn)
  have  : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
    field_simp <;> nlinarith
  linarith

/-- **The (min,+)-product in time `O(n^{3-δ} (log n)^{O(1)})`** from all-edges Exact Triangle in
time `n^{3-δ} (log n)^e`. -/
theorem minPlusInPolylog_of_explicitFrom {CA} (hCA : 0 ≤ CA) (hp : PairsFromAllEdges CA)
    {δ} {e} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ e) :
    (Claim.SolvedAlongPow lightModelAE.minPlusProduct UpperPowPolylog (3 - δ) : Prop) := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  intro κ hκ
  refine ⟨_, solvedIn_mp_of_allEdges hp hT, ?_⟩
  have hev := eventually_le_of_explicit hb (c := 54) (κ := κ) hκ
  have h1 :=
    isPowPolylog_logU_of_le (c := 1) fun n hn =>
      ⟨Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ, (one_mul _).ge⟩
  have h2 : IsPowPolylog (fun n => 1 + logU (6 * n ^ κ)) 0 :=
    (isPowPolylog_const 1).add (isPowPolylog_logU_mul_rpow (by norm_num) hκ)
  have h3 :=
    ((isPowPolylog_rpow_mul_log_pow (3 - δ) e).const_mul (κ + 1)).const_mul K
  have h4 : IsPowPolylog (fun n => n ^ 2) (3 - δ) :=
    (isBigOPow_natCast_pow 2).isPowPolylog.mono (by push_cast; linarith)
  have hg : IsPowPolylog (fun n => 1100 * (logU (n ^ κ) *
      (CA * ((1 + logU (6 * n ^ κ)) *
        (K * ((κ + 1) * (n ^ (3 - δ) * Real.log n ^ e)) + n ^ 2)) + n ^ 2)))
      (3 - δ) :=
    ((h1.mul ((((h2.mul (h3.add h4)).mono (by simp)).const_mul CA).add h4)).mono
      (by simp)).const_mul 1100
  refine hg.upperPowPolylog.mono_left ?_
  filter_upwards [hev] with n hn

  have  := logU_pos ((n : ℝ) ^ κ)
  have  := logU_pos (6 * (n : ℝ) ^ κ)
  simp only [(by ring : (9 : ℝ) * (6 * (n : ℝ) ^ κ) = 54 * (n : ℝ) ^ κ)]
  gcongr

/-- **APSP in time `O(n^{3-δ} (log n)^{O(1)})`** from all-edges Exact Triangle in time
`n^{3-δ} (log n)^e`: repeated squaring on top of the (min,+)-product. -/
theorem apspInPolylog_of_explicitFrom {CA} (hCA : 0 ≤ CA) (hp : PairsFromAllEdges CA)
    {δ} {e} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ e) :
    (Claim.SolvedAlongPow lightModelAE.apsp UpperPowPolylog (3 - δ) : Prop) := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  obtain ⟨c, C₀, hc, hsq⟩ := claim_apspFromMinPlus
  intro κ hκ
  refine ⟨_, hsq _ (solvedIn_mp_of_allEdges hp hT), ?_⟩
  have hev := eventually_le_of_explicit hb (c := 54 * c) (κ := κ + 1) (by linarith)
  -- the numbers `c n · n^κ = c n^{κ+1}` of the (min,+)-products, and `6` times them
  have hmag : ∀ n : ℕ, 1 ≤ n → 1 ≤ c * (n * n ^ κ) ∧
      c * (n * n ^ κ) ≤ c * n ^ (κ + 1) := fun n hn => by
    grind [Nat.one_le_cast, Real.one_le_rpow, one_le_mul_of_one_le_of_one_le, Real.rpow_add_one, mul_comm]

  have h1 :=
    isPowPolylog_logU_of_le hmag
  have h2 : IsPowPolylog (fun n => 1 + logU (6 * (c * (n * n ^ κ)))) 0 :=
    (isPowPolylog_const 1).add (isPowPolylog_logU_of_le (c := 6 * c) (κ := κ + 1) fun n hn =>
      ⟨one_le_mul_of_one_le_of_one_le (by norm_num) (hmag n hn).1,
        by grind⟩)
  have h3 :=
    ((isPowPolylog_rpow_mul_log_pow (3 - δ) e).const_mul (κ + 1 + 1)).const_mul K
  have h4 : IsPowPolylog (fun n => n ^ 2) (3 - δ) :=
    (isBigOPow_natCast_pow 2).isPowPolylog.mono (by push_cast; linarith)
  have h5 : IsPowPolylog
      (fun n => C₀ * (n ^ 2 * (1 + logU (c * (n * n ^ κ))))) (3 - δ) :=
    ((h4.mul ((isPowPolylog_const 1).add h1)).mono (by simp)).const_mul C₀
  have hg : IsPowPolylog (fun n => 6 * Real.log n *
      (1100 * (logU (c * (n * n ^ κ)) *
        (CA * ((1 + logU (6 * (c * (n * n ^ κ)))) *
          (K * ((κ + 1 + 1) * (n ^ (3 - δ) * Real.log n ^ e)) + n ^ 2)) +
            n ^ 2)) +
        C₀ * (n ^ 2 * (1 + logU (c * (n * n ^ κ)))))) (3 - δ) :=
    ((isPowPolylog_log.const_mul 6).mul ((((h1.mul ((((h2.mul (h3.add h4)).mono (by simp)).const_mul CA).add h4)).mono
      (by simp)).const_mul 1100).add h5)).mono (by simp)
  refine hg.upperPowPolylog.mono_left ?_
  filter_upwards [hev, eventually_ge_atTop 2] with n hn hn2
  have hn1 : 1 ≤ n := by omega


  rw [← (by
    rw [Real.rpow_add_one (by positivity)]
    ring
   : (9 : ℝ) * (6 * (c * ((n : ℝ) * (n : ℝ) ^ κ))) = 54 * c * (n : ℝ) ^ (κ + 1))] at hn

  have  := logU_pos (c * ((n : ℝ) * (n : ℝ) ^ κ))
  have  := logU_pos (6 * (c * ((n : ℝ) * (n : ℝ) ^ κ)))
  -- the time of the APSP program is nonnegative, so the factor next to `⌈log₂ n⌉ + 1` is

  exact mul_le_mul (clog_add_one_le n hn2) (by gcongr) (nonneg_of_mul_nonneg_right ((hsq _ (solvedIn_mp_of_allEdges hp hT)).nonneg hn1
    (Real.one_le_rpow (Nat.one_le_cast.2 hn1) hκ)
  ) (by positivity))
    (by positivity)

/-! ## The end statements -/

/-- The two end statements that all-edges Exact Triangle with the saving `δ` gives: the
(min,+)-product and APSP in `O(n^a)` steps on the word RAM for every exponent `a > 3 - δ`. -/
structure MinPlusSolved (δ : ℝ) : Prop where
  /-- The (min,+)-product in `O(n^a)` steps for every `a > 3 - δ`. -/
  minPlus : ∀ a , 3 - δ < a → SolvedInTime EndStatement.MinPlusProduct a 0
  /-- APSP in `O(n^a)` steps for every `a > 3 - δ`. -/
  apsp : ∀ a , 3 - δ < a → SolvedInTime EndStatement.APSP a 0

/-- **From all-edges Exact Triangle in time `n^{3-δ} (log n)^e` to the end statements.** -/
theorem minPlusSolved_of_explicitFrom {CA} (hCA : 0 ≤ CA) (hp : PairsFromAllEdges CA)
    {δ} {e} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ e) : MinPlusSolved δ :=
  ⟨fun _ ha => (FromClaims.solvedInPolylogTime_of_claim (fun T hT => realized_minPlusProduct T hT) (minPlusInPolylog_of_explicitFrom hCA hp hδ h) : SolvedInPolylogTime EndStatement.MinPlusProduct (3 - δ)).solvedInTime ha,
    fun _ ha => (FromClaims.solvedInPolylogTime_of_claim (fun T hT => realized_apsp T hT) (apspInPolylog_of_explicitFrom hCA hp hδ h) : SolvedInPolylogTime EndStatement.APSP (3 - δ)).solvedInTime ha⟩

end ImprovedExponents.AllEdges
