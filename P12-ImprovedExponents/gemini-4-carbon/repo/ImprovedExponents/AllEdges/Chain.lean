module

public import ImprovedExponents.AllEdges.Model
public import ImprovedExponents.AllEdges.Host.BruteAE
public import ImprovedExponents.Pipeline.HostBound
public import ThreeSumApsp.RunningTimes.Sec3.Theorem22
public import ThreeSumApsp.Lang.PolyBounded

@[expose] public section

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam Filter

def PairsFromAllEdges (CA : ℝ) : Prop :=
  ∀ T : ℕ → ℝ → ℝ, SolvedIn aeTask T →
    SolvedIn pairsTask fun n u => CA * ((1 + logU u) * (T n (9 * u) + (n : ℝ) ^ 2))

theorem solvedIn_mp_of_allEdges {CA : ℝ} (hp : PairsFromAllEdges CA) {T : ℕ → ℝ → ℝ}
    (h : SolvedIn aeTask T) :
    SolvedIn mpTask fun n u => 1100 * (logU u *
      (CA * ((1 + logU (6 * u)) * (T n (9 * (6 * u)) + (n : ℝ) ^ 2)) + (n : ℝ) ^ 2)) := by
  refine isHost_mp.solvedIn (hp T h) fun Tn hTn n U u hn hU hu => ?_
  have hR := MinPlusFromNeg.mpRounds_le hU hu
  have hL : 1 / 2 < logU u := Real.one_half_lt_log_two.trans_le (log_two_le_logU u)
  have hT := hTn n (6 * U) (6 * u) hn (by omega) (by push_cast; linarith)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  simp  [mpTime]; push_cast; rw [← sq (n : ℝ)]
  nlinarith 

theorem _root_.Light.SolvedIn.nonneg {task : Task} {T : ℕ → ℝ → ℝ} (h : SolvedIn task T) {n : ℕ}
    {u : ℝ} (hn : 1 ≤ n) (hu : 1 ≤ u) : 0 ≤ T n u := by
  obtain ⟨_, _, Tn, _, -, -, hT⟩ := h
  exact (Nat.cast_nonneg (Tn n 1)).trans (hT n 1 u hn le_rfl (by grind))

private theorem eventually_le_of_explicit {n₀ : ℕ} {K δ : ℝ} {e : ℕ} {T : ℕ → ℝ → ℝ}
    (hb : ∀ (n : ℕ) (κ u : ℝ), n₀ ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)))
    {c κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ᶠ n : ℕ in atTop,
      T n (c * (n : ℝ) ^ κ) ≤ K * ((κ + 1) * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) := by
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop ⌈c⌉₊, eventually_ge_atTop 1] with n
    hn₀ hnc hn1
  refine hb n (κ + 1) _ hn₀ (by linarith) ?_
  rw [Real.rpow_add_one (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_left ((Nat.le_ceil c).trans (by exact_mod_cast hnc)) (by positivity)

private theorem isPowPolylog_mpShape {CA K δ : ℝ} {e : ℕ} (hδ : δ ≤ 1) {u : ℕ → ℝ} {c κ : ℝ}
    (hmag : ∀ n : ℕ, 1 ≤ n → 1 ≤ u n ∧ u n ≤ c * (n : ℝ) ^ κ) :
    IsPowPolylog (fun n : ℕ => 1100 * (logU (u n) *
      (CA * ((1 + logU (6 * u n)) *
        (K * ((κ + 1) * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) + (n : ℝ) ^ 2)) + (n : ℝ) ^ 2)))
      (3 - δ) := by
  have h1 : IsPowPolylog (fun n : ℕ => logU (u n)) 0 := isPowPolylog_logU_of_le hmag
  have h2 : IsPowPolylog (fun n : ℕ => 1 + logU (6 * u n)) 0 :=
    (isPowPolylog_const 1).add (isPowPolylog_logU_of_le (c := 6 * c) (κ := κ) fun n hn =>
      ⟨one_le_mul_of_one_le_of_one_le (by norm_num) (hmag n hn).1,
        by grind⟩)
  have h3 : IsPowPolylog (fun n : ℕ => K * ((κ + 1) * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))) (3 - δ) :=
    ((isPowPolylog_rpow_mul_log_pow (3 - δ) e).const_mul (κ + 1)).const_mul K
  have h4 : IsPowPolylog (fun n : ℕ => (n : ℝ) ^ 2) (3 - δ) :=
    (isBigOPow_natCast_pow 2).isPowPolylog.mono (by push_cast; linarith)
  exact ((h1.mul ((((h2.mul (h3.add h4)).mono (by simp)).const_mul CA).add h4)).mono (by simp)).const_mul 1100

structure MinPlusSolved (δ : ℝ) : Prop where
  minPlus : ∀ a : ℝ, 3 - δ < a → SolvedInTime EndStatement.MinPlusProduct a 0
  apsp : ∀ a : ℝ, 3 - δ < a → SolvedInTime EndStatement.APSP a 0

theorem minPlusSolved_of_explicitFrom {CA : ℝ} (hCA : 0 ≤ CA) (hp : PairsFromAllEdges CA)
    {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ e) : MinPlusSolved δ := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  have hmp : Claim.MinPlusInPolylog lightModelAE (3 - δ) := fun κ hκ => by
    refine ⟨_, solvedIn_mp_of_allEdges hp hT, (isPowPolylog_mpShape (CA := CA) (K := K) (e := e)
      hδ (u := fun n => (n : ℝ) ^ κ) (c := 1) (κ := κ) fun n hn =>
        ⟨Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ, (one_mul _).ge⟩).upperPowPolylog.mono_left ?_⟩
    filter_upwards [eventually_le_of_explicit hb (c := 54) hκ] with n hn
    simp only [show (9 : ℝ) * (6 * (n : ℝ) ^ κ) = 54 * (n : ℝ) ^ κ by ring]
    have := logU_pos ((n : ℝ) ^ κ); have := logU_pos (6 * (n : ℝ) ^ κ); gcongr
  have hap : Claim.ApspInPolylog lightModelAE (3 - δ) := by
    obtain ⟨c, C₀, hc, hsq⟩ := claim_apspFromMinPlus
    intro κ hκ
    have hmag (n : ℕ) (hn : 1 ≤ n) : 1 ≤ c * ((n : ℝ) * (n : ℝ) ^ κ) ∧
        c * ((n : ℝ) * (n : ℝ) ^ κ) ≤ c * (n : ℝ) ^ (κ + 1) := by
      have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
      exact ⟨one_le_mul_of_one_le_of_one_le hc (one_le_mul_of_one_le_of_one_le hn1 (Real.one_le_rpow hn1 hκ)),
        by rw [Real.rpow_add_one (by positivity), mul_comm (n : ℝ)]⟩
    have h0 : IsPowPolylog (fun n : ℕ => 6 * Real.log n) 0 := isPowPolylog_log.const_mul 6
    have h4 : IsPowPolylog (fun n : ℕ => (n : ℝ) ^ 2) (3 - δ) :=
      (isBigOPow_natCast_pow 2).isPowPolylog.mono (by push_cast; linarith)
    have h5 : IsPowPolylog (fun n : ℕ => C₀ * ((n : ℝ) ^ 2 * (1 + logU (c * ((n : ℝ) * (n : ℝ) ^ κ))))) (3 - δ) :=
      ((h4.mul ((isPowPolylog_const 1).add (isPowPolylog_logU_of_le hmag))).mono (by simp)).const_mul C₀
    have hg : IsPowPolylog _ (3 - δ) := (h0.mul ((isPowPolylog_mpShape (CA := CA) (K := K) (e := e)
      (u := fun n => c * ((n : ℝ) * (n : ℝ) ^ κ)) (c := c) (κ := κ + 1)
      hδ hmag).add h5)).mono (by simp)
    refine ⟨_, hsq _ (solvedIn_mp_of_allEdges hp hT), hg.upperPowPolylog.mono_left ?_⟩
    filter_upwards [eventually_le_of_explicit hb (c := 54 * c) (κ := κ + 1) (by linarith),
      eventually_ge_atTop 2] with n hn hn2
    have hn1 : 1 ≤ n := by omega
    rw [← show (9 : ℝ) * (6 * (c * ((n : ℝ) * (n : ℝ) ^ κ))) = 54 * c * (n : ℝ) ^ (κ + 1) by
      rw [Real.rpow_add_one (by positivity)]; ring] at hn
    have hclog : (Nat.clog 2 n : ℝ) + 1 ≤ 6 * Real.log n := by
      have hcl : (Nat.clog 2 n : ℝ) < Real.log n / Real.log 2 + 1 := by
        simpa [Real.logb] using Real.natCast_clog_lt_logb_add_one 2 n
      have hlog2 := Real.one_half_lt_log_two
      have hlogn := Real.log_le_log two_pos (by exact_mod_cast hn2 : (2 : ℝ) ≤ n)
      have hdiv : Real.log n / Real.log 2 ≤ 2 * Real.log n := (div_le_iff₀ (by linarith)).2 (by nlinarith)
      linarith
    have := logU_pos (c * ((n : ℝ) * (n : ℝ) ^ κ))
    have := logU_pos (6 * (c * ((n : ℝ) * (n : ℝ) ^ κ)))
    have hX0 := (hsq _ (solvedIn_mp_of_allEdges hp hT)).nonneg hn1 (Real.one_le_rpow (Nat.one_le_cast.2 hn1) hκ)
    exact mul_le_mul hclog (by gcongr) (nonneg_of_mul_nonneg_right hX0 (by positivity)) (by positivity)
  exact ⟨fun _ ha => (FromClaims.solvedInPolylogTime_of_claim (fun T hT => realized_minPlusProduct T hT) hmp).solvedInTime ha,
    fun _ ha => (FromClaims.solvedInPolylogTime_of_claim (fun T hT => realized_apsp T hT) hap).solvedInTime ha⟩

private theorem exists_aeFlags_eq_one_iff (n : ℕ) (AB BC AC : List ℤ) :
    (∃ q < n * n, (aeFlags n AB BC AC).getD q 0 = 1) ↔ (triOf n AB BC AC).HasZeroTriangle := by
  constructor
  · rintro ⟨q, hq, h1⟩
    have hn : 0 < n := by nlinarith
    rw [aeFlags_getD _ _ _ hq] at h1
    unfold flag at h1; split_ifs at h1 with hc; swap; · norm_num at h1
    obtain ⟨c, hc, h0⟩ := hc
    exact ⟨⟨q / n, Nat.div_lt_of_lt_mul (by linarith)⟩, ⟨q % n, Nat.mod_lt _ hn⟩, ⟨c, hc⟩,
      by simpa [triOf, TriangleInstance.IsZeroTriangle, TriangleInstance.S,
        show q / n * n + q % n = q by linarith [Nat.div_add_mod q n]] using h0⟩
  · rintro ⟨a, b, c, h⟩
    have hq : a.1 * n + b.1 < n * n := by nlinarith [a.2, b.2]
    refine ⟨a.1 * n + b.1, hq, ?_⟩
    rw [aeFlags_getD _ _ _ hq,
      show (a.1 * n + b.1) / n = a.1 by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt b.2, zero_add],
      show (a.1 * n + b.1) % n = b.1 by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.2]]
    exact ite_eq_left ⟨c.1, c.2, by simpa [triOf, TriangleInstance.IsZeroTriangle, TriangleInstance.S] using h⟩

def etFromAEBody (pAE : ℕ) : Stmt :=
  .set 6 (v 0 *' v 0) ;;
  .call pAE [v 0, v 1, v 2, v 3, v 4, v 5, v 5 +' v 6] 0 ;;
  .set 0 (k 0) ;;
  .set 7 (k 0) ;;
  .while (v 7 <' v 6) (
    .ite (M (v 5 +' v 7) =' k 1) (.set 0 (k 1)) .skip ;;
    .set 7 (v 7 +' k 1))

def etFromAETime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := T n U + 30 * (n * n) + 80

def etFromAENeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨(r n U).word + n * n + U + 2, (r n U).cells + n * n, (r n U).depth + 1⟩

theorem isHost_et_of_ae : IsHost aeTask etTask etFromAETime etFromAENeed := by
  refine ⟨fun P₀ pAE T r hsol => ⟨[etFromAEBody pAE], P₀.length, etFromAEBody pAE, by simp,
    fun R lim d (x : TriInst) μ fr (hpre : x.Pre μ fr)
      (hok : (etFromAENeed r x.n x.U).Ok lim fr d) => ?_⟩,
    fun r h => by unfold etFromAENeed; poly_need [h.word, h.cells, h.depth]⟩
  rw [List.append_assoc]
  have hw := hok.space
  have hcells : fr + ((r x.n x.U).cells + x.n * x.n) ≤ lim.space := hok.cells
  have hdepth : d + ((r x.n x.U).depth + 1) ≤ lim.depth := hok.depth
  have hn2 : ((x.n * x.n : ℕ) : ℤ) = (x.n : ℤ) * x.n := by push_cast; rfl
  have hfrw : ((fr + x.n * x.n : ℕ) : ℤ) = (fr : ℤ) + (x.n * x.n : ℕ) := by push_cast; rfl
  change Ends lim (P₀ ++ ([etFromAEBody pAE] ++ R)) d (etFromAEBody pAE)
    ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ (etFromAETime T x.n x.U) _
  rw [← frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr] 2]
  unfold etFromAEBody etFromAETime
  light_set (x.n * x.n : ℕ) using hn2
  have hapre : (⟨x.n, x.U, x.ab, x.bc, x.ac, fr, x.AB, x.BC, x.AC⟩ : AeInst).Pre μ (fr + x.n * x.n) :=
    ⟨hpre.n_pos, hpre.U_pos, hpre.lenAB, hpre.lenBC, hpre.lenAC, hpre.segAB, hpre.segBC, hpre.segAC,
      hpre.leAB, hpre.leBC, hpre.leAC, hpre.belowAB.trans (Nat.le_add_right _ _),
      hpre.belowBC.trans (Nat.le_add_right _ _), hpre.belowAC.trans (Nat.le_add_right _ _), le_rfl⟩
  have haok : (r x.n x.U).Ok lim (fr + x.n * x.n) (d + 1) :=
    hok.mono (by simp [etFromAENeed]; omega) (by simp [etFromAENeed]; omega)
      (by simp [etFromAENeed]; omega)
  refine Ends.callToThen (hsol.meets ([etFromAEBody pAE] ++ R)
    ⟨x.n, x.U, x.ab, x.bc, x.ac, fr, x.AB, x.BC, x.AC⟩ (fr + x.n * x.n) hapre haok) ?_
    (ha := by have := hpre.belowAB; have := hpre.belowBC; have := hpre.belowAC; light_side [aeTask, hfrw])
    (hd := by omega) (hT := by simp [aeTask]; omega)
  rintro r₁ μ₁ ⟨hseg, hkept⟩
  simp only at hseg hkept
  light_set (0 : ℕ) using aeTask
  light_set (0 : ℕ) using aeTask
  refine Ends.whileBlock (fun j σ =>
    σ = ⟨frame [flag (∃ i < j, (aeFlags x.n x.AB x.BC x.AC).getD i 0 = 1),
      x.U, x.ab, x.bc, x.ac, fr, (x.n * x.n : ℕ), j], μ₁⟩) (x.n * x.n)
    (by simp [flag]) ?round ?done (by dsimp [aeTask]; simp; omega)
  case round =>
    rintro j _ hj rfl
    have hjlen : j < (aeFlags x.n x.AB x.BC x.AC).length := by simp [hj]
    have hread : μ₁ (fr + j) = (aeFlags x.n x.AB x.BC x.AC).getD j 0 := by
      rw [hseg j hjlen, List.getD_eq_getElem _ _ hjlen]
    have h01 : (aeFlags x.n x.AB x.BC x.AC).getD j 0 = 0 ∨ (aeFlags x.n x.AB x.BC x.AC).getD j 0 = 1 := by
      rw [aeFlags_getD _ _ _ hj]; unfold flag; split_ifs <;> simp
    have hf01 : |flag (∃ i < j, (aeFlags x.n x.AB x.BC x.AC).getD i 0 = 1)| ≤ lim.word := by
      unfold flag; split_ifs <;> simp <;> omega
    generalize hfv : (aeFlags x.n x.AB x.BC x.AC).getD j 0 = fv at hread h01
    refine ⟨by light_side, by simp; exact_mod_cast hj, ?_⟩
    by_cases h1 : fv = 1
    · have hnext : flag (∃ i < j + 1, (aeFlags x.n x.AB x.BC x.AC).getD i 0 = 1) = 1 :=
        ite_eq_left ⟨j, Nat.lt_succ_self j, hfv.trans h1⟩
      refine Stmt.Runs.seq (Stmt.Runs.ite_pos ⟨by light_side, ?_⟩ (by light_side [hread, h1])
        (by light_side [hread, h1]))
      exact ⟨by light_side, by rw [hnext]; simp [update_frame_setLocal]⟩
    · have h0 : fv = 0 := h01.resolve_right h1
      have hnext : flag (∃ i < j + 1, (aeFlags x.n x.AB x.BC x.AC).getD i 0 = 1) =
          flag (∃ i < j, (aeFlags x.n x.AB x.BC x.AC).getD i 0 = 1) := flag_congr (by grind)
      refine Stmt.Runs.seq (Stmt.Runs.ite_neg ⟨trivial, ?_⟩ (by light_side [hread, h0])
        (by light_side [hread, h0]))
      exact ⟨by light_side, by rw [hnext]; simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by simp,
      by simpa using flag_congr (exists_aeFlags_eq_one_iff x.n x.AB x.BC x.AC),
      fun a ha => hkept a ⟨by omega, Or.inl ha⟩⟩

theorem explicitFrom_light_of_ae {δ : ℝ} (hδ : δ ≤ 1) (h : ExplicitFrom lightModelAE δ 1) :
    ExplicitFrom lightModel δ 1 := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  refine ⟨max n₀ 3, |K| + 110, fun n u => T n u + 30 * (n : ℝ) ^ 2 + 80,
    isHost_et_of_ae.solvedIn hT (fun Tn hTn n U u hn hU hu => by
      have := hTn n U u hn hU hu
      simp  [etFromAETime]; push_cast; rw [← sq (n : ℝ)]; linarith),
    fun n κ u hn hκ hu => ?_⟩
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le hn3
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (3 - δ) := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)
  have hS1 : (1 : ℝ) ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1) := by
    rw [pow_one]; exact one_le_mul_of_one_le_of_one_le hκ
      (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hn1 (by linarith)) hlog)
  have hSn2 : (n : ℝ) ^ 2 ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1) := by
    rw [pow_one]
    exact hpow.trans ((le_mul_of_one_le_right (by positivity) hlog).trans
      (le_mul_of_one_le_left (by positivity) hκ))
  have hTK : T n u ≤ |K| * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1)) :=
    (hb n κ u hn₀ hκ hu).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith))
  linarith

theorem claim_bruteForce_ae : Claim.BruteForce lightModel := by
  have hs : SolvedIn aeTask fun n _ => ((tBruteAE n + copyTime (n * n) + 40 : ℕ) : ℝ) :=
    ⟨_, _, _, _, by poly_need [], bruteAE_solves, fun _ _ _ _ _ _ => le_rfl⟩
  refine ⟨450, isHost_et_of_ae.solvedIn hs fun Tn hTn n U u hn hU hu => ?_⟩
  have h1 := hTn n U u hn hU hu
  have hlog : 0 ≤ logU u := (logU_pos u).le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp  [etFromAETime, tBruteAE] at h1 ⊢
  push_cast at h1 ⊢; rw [← sq (n : ℝ)] at h1 ⊢
  nlinarith [mul_nonneg hlog (show (0 : ℝ) ≤ (n : ℝ) ^ 3 by positivity)]

end ImprovedExponents.AllEdges
