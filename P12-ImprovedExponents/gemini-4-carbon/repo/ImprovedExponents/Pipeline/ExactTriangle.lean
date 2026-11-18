module

public import ThreeSumApsp.RunningTimes.Sec3.Theorem22
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ImprovedExponents.Pipeline.HostBound
public import ImprovedExponents.ParamRoutines

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam Light Light.Sec3 Light.Sec4 ParamRoutines
  Filter

structure AllSolved (δ : ℝ) : Prop where
  exactTriangle : ∀ a : ℝ, 3 - δ < a → SolvedInTime EndStatement.ExactTriangle a 0
  threeSum : ∀ a : ℝ, 2 - δ / 2 < a → SolvedInTime EndStatement.ThreeSum a 0

theorem exactTriangle_of_explicitFrom {δ : ℝ} {e : ℕ} (h : ExplicitFrom lightModel δ e) {a : ℝ}
    (ha : 3 - δ < a) : SolvedInTime EndStatement.ExactTriangle a 0 := by
  obtain ⟨n₀, K, T, hT, hb⟩ := h
  refine FromClaims.solvedInTime_of_claim realized_exactTriangle fun κ _ =>
    ⟨T, hT, UpperPowPolylog.upperBigOPow ⟨K * max κ 1, e, ?_⟩ ha⟩
  filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  exact (hb n (max κ 1) ((n : ℝ) ^ κ) ((le_max_left _ _).trans hn) (le_max_right _ _)
    (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _))).trans_eq (by ring)

theorem allSolved_of_uniform {δ : ℝ} {e : ℕ} (hδ1 : δ ≤ 1) (hex : ExplicitFrom lightModel δ e)
    (hu : Claim.ExactTriangleUniform lightModel δ e) : AllSolved δ :=
  ⟨fun _ ha => exactTriangle_of_explicitFrom hex ha, fun _ ha => threeSum_of_uniform hδ1 hu ha⟩

def MidHostRat (M : DetTimeModel) : Prop :=
  ∀ a b c d : ℕ, 1 ≤ b → 1 ≤ d → a ≤ 2 * b → c ≤ 3 * d →
    HostBound M strassen (paramDRat a b) (paramGRatOf a b c d)
      (fun n => pieceSizeNat (paramDRat a b n) (paramGRatOf a b c d n)
        * Nat.sqrt (paramDRat a b n))

theorem lopClaim_of_thinClaim_light {ε γ q : ℝ} (hthin : ThinClaim lightModel ε γ q) (hγ : 0 ≤ γ)
    (hq : 0 ≤ q) (hε : ε * (1 + γ) ≤ 1) {M : DetTimeModel}
    (hM : M.lopDetect = lightModel.lopDetect) : LopClaim M ε γ q := by
  obtain ⟨C, T, hT, hb⟩ := hthin
  obtain ⟨C₁, hlop⟩ := claim_lopCountFromThinProduct
  obtain ⟨C₃, hdet⟩ := claim_lopDetectFromCount
  refine ⟨|C| + 2 * |C₁| + |C₃|, _, by rw [hM]; exact hdet _ (hlop T hT), fun n D w hn hD hDn => ?_⟩
  have hNR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hnD : (n : ℝ) * D ≤ preBound31 γ n D := by
    have hpow : (D : ℝ) * (D : ℝ) ^ γ ≤ n := by
      rw [← Real.rpow_one_add' hD0.le (by linarith)]
      exact (Real.rpow_le_rpow hD0.le hDn (by linarith)).trans
        ((Real.rpow_mul (by positivity) _ _).symm.trans_le
          ((Real.rpow_le_rpow_of_exponent_le hNR hε).trans_eq (Real.rpow_one _)))
    rw [preBound31, le_div_iff₀ (Real.rpow_pos_of_pos hD0 _)]
    calc (n : ℝ) * D * (D : ℝ) ^ γ = n * (D * (D : ℝ) ^ γ) := by ring
      _ ≤ (n : ℝ) ^ 2 * 1 := by nlinarith
      _ ≤ (n : ℝ) ^ 2 * (Real.log D + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith [Real.log_nonneg hDR])) (by positivity)
  have hq1 : 1 ≤ queryBound31 q D := one_le_queryBound31 hD hq
  have h1 : T n D w 1 ≤ |C| * (preBound31 γ n D + w * queryBound31 q D) :=
    (hb n D w 1 hn hD hDn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by nlinarith))
  have h2 : C₁ * ((n : ℝ) * D + w + 1) ≤ |C₁| * (2 * (preBound31 γ n D + w * queryBound31 q D)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₁) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _))
  have h3 : C₃ * ((w : ℝ) + 1) ≤ |C₃| * (preBound31 γ n D + w * queryBound31 q D) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₃) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _))
  linarith

noncomputable abbrev uniformShape (δ : ℝ) (e : ℕ) (p : SizeBound) : ℝ :=
  (p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e * (1 + logU p.u) ^ 2

theorem allSolved_of_explicitFrom {δ : ℝ} {e : ℕ} (hbf0 : Claim.BruteForce lightModel)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hex : ExplicitFrom lightModel δ e) : AllSolved δ := by
  refine allSolved_of_uniform hδ1 hex ?_
  obtain ⟨n₀, K, T, hT, hb⟩ := hex
  obtain ⟨C, hbf⟩ := hbf0
  obtain ⟨C₀, hch⟩ := closure_chooseBySize (max n₀ 3)
  have hm0 : n₀ ≤ max n₀ 3 := le_max_left _ _
  have hm3 : 3 ≤ max n₀ 3 := le_max_right _ _
  generalize max n₀ 3 = n₁ at hch hm0 hm3
  have hshape (p : SizeBound) (hp : 1 ≤ p.s ∧ 1 ≤ p.u) : 1 ≤ uniformShape δ e p :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (Nat.one_le_cast.2 hp.1) (by linarith)) (one_le_log_add_one_pow p.s e))
      (one_le_pow₀ (one_le_one_add_logU p.u))
  have hsmall : Dominated (fun p : SizeBound => (1 ≤ p.s ∧ 1 ≤ p.u) ∧ p.s < n₁)
      (fun p => C * ((p.s : ℝ) ^ 3 * (1 + logU p.u))) (uniformShape δ e) := by
    refine (Dominated.of_le_const_mul (C := (n₁ : ℝ) ^ δ) (by positivity) fun p hp => ?_)
      |>.const_mul_of_nonneg C fun p _ =>
        mul_nonneg (by positivity) (zero_le_one.trans (one_le_one_add_logU p.u))
    have hs0 : (0 : ℝ) < p.s := Nat.cast_pos.2 hp.1.1
    have hsplit : (p.s : ℝ) ^ 3 = (p.s : ℝ) ^ δ * (p.s : ℝ) ^ (3 - δ) := by
      rw [← Real.rpow_add hs0, ← Real.rpow_natCast]; congr 1; ring
    have := one_le_log_add_one_pow p.s e
    have := one_le_one_add_logU p.u
    have := Real.rpow_le_rpow hs0.le (Nat.cast_le.2 hp.2.le) hδ0
    calc (p.s : ℝ) ^ 3 * (1 + logU p.u)
        = (p.s : ℝ) ^ δ * ((p.s : ℝ) ^ (3 - δ) * 1 * (1 + logU p.u) ^ 1) := by rw [hsplit]; ring
      _ ≤ (n₁ : ℝ) ^ δ * ((p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e * (1 + logU p.u) ^ 2) := by
          gcongr; norm_num
  have hbig : Dominated (fun p : SizeBound => (1 ≤ p.s ∧ 1 ≤ p.u) ∧ ¬ p.s < n₁)
      (fun p => T p.s p.u) (uniformShape δ e) := by
    refine (Dominated.of_exists_const (g := fun p => max 1 (Real.log p.u / Real.log p.s) *
      ((p.s : ℝ) ^ (3 - δ) * Real.log p.s ^ e)) ⟨K, fun p hp => ?_⟩ fun _ _ => by positivity).trans
      (.of_le fun p hp => ?_)
    · have hs3 : 3 ≤ p.s := hm3.trans (not_lt.1 hp.2)
      have hs0 : (0 : ℝ) < p.s := Nat.cast_pos.2 (by omega)
      have hlogs := Real.one_le_log_natCast_of_three_le hs3
      refine hb p.s _ p.u (hm0.trans (not_lt.1 hp.2)) (le_max_left _ _) ?_
      calc p.u = (p.s : ℝ) ^ (Real.log p.u / Real.log p.s) := by
            rw [Real.rpow_def_of_pos hs0, mul_div_cancel₀ _ (by linarith),
              Real.exp_log (zero_lt_one.trans_le hp.1.2)]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hp.1.1) (le_max_right _ _)
    · have hs3 : 3 ≤ p.s := hm3.trans (not_lt.1 hp.2)
      have hκ1 : max 1 (Real.log p.u / Real.log p.s) ≤ 1 + logU p.u := by
        refine max_le (one_le_one_add_logU p.u) ?_
        linarith [div_le_self (Real.log_nonneg hp.1.2) (Real.one_le_log_natCast_of_three_le hs3),
          log_le_logU (zero_lt_one.trans_le hp.1.2)]
      have hκ := hκ1.trans (le_self_pow₀ (one_le_one_add_logU p.u) two_ne_zero)
      calc max 1 (Real.log p.u / Real.log p.s) * ((p.s : ℝ) ^ (3 - δ) * Real.log p.s ^ e)
          ≤ (1 + logU p.u) ^ 2 * ((p.s : ℝ) ^ (3 - δ) * (Real.log p.s + 1) ^ e) := by
            gcongr; linarith
        _ = uniformShape δ e p := by ring
  obtain ⟨K', hK'0, hK'⟩ := (Dominated.ite hsmall hbig fun p hp =>
    zero_le_one.trans (hshape p hp)).add (.const C₀ hshape)
  refine ⟨1 + K', le_add_of_nonneg_right hK'0,
    SolvedIn.mono (hch _ T hbf hT) fun s u hs hu => ?_⟩
  exact (hK' ⟨s, u⟩ ⟨hs, hu⟩).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
    (zero_le_one.trans (hshape ⟨s, u⟩ ⟨hs, hu⟩)))

private structure MidStep (d η ε γ q K₁ K₂ : ℝ) (n Dn gn Dcn : ℕ) : Prop where
  hn3 : 3 ≤ n
  sixteen_le : 16 ≤ Dn
  le_n : Dn ≤ n
  one_le_g : 1 ≤ gn
  g_le_sqrt : (gn : ℝ) ≤ Real.sqrt Dn
  D_le : (Dn : ℝ) ≤ (n : ℝ) ^ d
  g_le : (gn : ℝ) ≤ 2 * (n : ℝ) ^ (d * η)
  inv_g_le : 1 / (gn : ℝ) ≤ 2 * (n : ℝ) ^ (-(d * η))
  cap_le : (n : ℝ) ^ 2 / Real.sqrt Dn ≤ 2 * (n : ℝ) ^ (2 + -(d / 2))
  dc_one : 1 ≤ Dcn
  dc_eps : (Dcn : ℝ) ≤ (n : ℝ) ^ ε
  dc_n : (Dcn : ℝ) ≤ n
  dc_neg : (Dcn : ℝ) ^ (-γ) ≤ K₁ * (n : ℝ) ^ (d * (1 - η) * -γ)
  dc_pos : (Dcn : ℝ) ^ q ≤ K₂ * (n : ℝ) ^ (d * (1 - η) * q)

private lemma pieceSize_bounds {η : ℝ} {Dn gn : ℕ} (h16 : 16 ≤ Dn) (hg1 : 1 ≤ gn)
    (hgs : (gn : ℝ) ≤ Real.sqrt Dn) (hgl : (Dn : ℝ) ^ η ≤ gn) (hgu : (gn : ℝ) ≤ 2 * (Dn : ℝ) ^ η) :
    1 / 8 * (Dn : ℝ) ^ (1 - η) ≤ ((pieceSizeNat Dn gn * Nat.sqrt Dn : ℕ) : ℝ) ∧
      ((pieceSizeNat Dn gn * Nat.sqrt Dn : ℕ) : ℝ) ≤ 2 * (Dn : ℝ) ^ (1 - η) := by
  have hX0 : (0 : ℝ) < Dn := by exact_mod_cast (by omega : 0 < Dn)
  have hg0 : (0 : ℝ) < gn := by exact_mod_cast hg1
  have hS1 : (Nat.sqrt Dn : ℝ) ≤ Real.sqrt Dn := Real.nat_sqrt_le_real_sqrt
  have hS2 : Real.sqrt Dn < (Nat.sqrt Dn : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hgS : (gn : ℝ) ≤ Nat.sqrt Dn := by
    exact_mod_cast (by rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]; exact Nat.le_floor hgs : gn ≤ _)
  have hS0 : (0 : ℝ) ≤ Nat.sqrt Dn := Nat.cast_nonneg _
  have hpiece : pieceSizeNat Dn gn = ⌈(Nat.sqrt Dn : ℝ) / gn⌉₊ :=
    (Nat.ceil_div_eq_ceilDiv _ hg1).symm
  have hPl : (Nat.sqrt Dn : ℝ) / gn ≤ pieceSizeNat Dn gn := by rw [hpiece]; exact Nat.le_ceil _
  have hPu : (pieceSizeNat Dn gn : ℝ) < (Nat.sqrt Dn : ℝ) / gn + 1 := by
    rw [hpiece]; exact Nat.ceil_lt_add_one (by positivity)
  have hq1 : 1 ≤ (Nat.sqrt Dn : ℝ) / gn := (one_le_div hg0).2 hgS
  have hSS : (Nat.sqrt Dn : ℝ) * Nat.sqrt Dn ≤ Dn :=
    (mul_le_mul hS1 hS1 hS0 (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hX0.le)
  have hSS' : (Dn : ℝ) / 4 ≤ (Nat.sqrt Dn : ℝ) * Nat.sqrt Dn := by
    have hg1' : (1 : ℝ) ≤ gn := by exact_mod_cast hg1
    have h1 : Real.sqrt Dn / 2 ≤ Nat.sqrt Dn := by linarith
    nlinarith [mul_le_mul h1 h1 (by positivity) hS0, Real.mul_self_sqrt hX0.le]
  rw [Real.rpow_sub hX0, Real.rpow_one, Nat.cast_mul]
  exact ⟨(by ring : 1 / 8 * ((Dn : ℝ) / (Dn : ℝ) ^ η) = (Dn : ℝ) / 4 / (2 * (Dn : ℝ) ^ η)).trans_le <|
      (div_le_div₀ (by positivity) hSS' hg0 hgu).trans <|
      (by ring : _ = (Nat.sqrt Dn : ℝ) / gn * Nat.sqrt Dn).trans_le
        (mul_le_mul_of_nonneg_right hPl hS0),
    (mul_le_mul_of_nonneg_right (by linarith : (pieceSizeNat Dn gn : ℝ) ≤ 2 * (Nat.sqrt Dn / gn))
      hS0).trans <| (by ring : _ = 2 * ((Nat.sqrt Dn : ℝ) * Nat.sqrt Dn / gn)).trans_le <|
      mul_le_mul_of_nonneg_left (div_le_div₀ hX0.le hSS (by positivity) hgl) (by norm_num)⟩

private lemma exists_midStep {d η ε γ q : ℝ} {D g : ℕ → ℕ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hη0 : 0 < η) (hη1 : η < 1 / 2) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hthin : d * (1 - η) < ε)
    (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊) :
    ∃ (n₀ : ℕ) (K₁ K₂ : ℝ), 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ n ≥ n₀,
      MidStep d η ε γ q K₁ K₂ n (D n) (g n) (pieceSizeNat (D n) (g n) * Nat.sqrt (D n)) := by
  set a := 1 - η
  have ha0 : 0 < a := by linarith
  have hda1 : d * a < 1 := by nlinarith
  have hτ0 : 0 < 1 / 2 - η := by linarith
  have hτ1 : 0 < min ε 1 - d * a := sub_pos.2 (lt_min hthin hda1)
  have hc₀ : 0 < (1 / 8 : ℝ) / (2 : ℝ) ^ a := by positivity
  have ev_pow {b : ℝ} (hb : 0 < b) (B : ℝ) : ∀ᶠ n : ℕ in atTop, B ≤ (n : ℝ) ^ b :=
    ((tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 <|
    (ev_pow hd0 (max 16 (2 * (2 : ℝ) ^ (1 / (1 / 2 - η))))).and <|
    (ev_pow hτ1 2).and (eventually_ge_atTop 3)
  refine ⟨n₀, ((1 / 8 : ℝ) / (2 : ℝ) ^ a) ^ (-γ), (2 : ℝ) ^ q, by positivity, by positivity,
    fun n hn => ?_⟩
  obtain ⟨hn_d, hn_a, hn3⟩ := hn₀ n hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hN0 : (0 : ℝ) < n := by linarith
  have hfl : (D n : ℝ) ≤ (n : ℝ) ^ d := by rw [hD]; exact Nat.floor_le (by positivity)
  have hlt : (n : ℝ) ^ d < (D n : ℝ) + 1 := by rw [hD]; exact Nat.lt_floor_add_one _
  have hD16 : 16 ≤ D n := by
    rw [hD]; exact Nat.le_floor (by exact_mod_cast (le_max_left _ _).trans hn_d)
  have hX16 : (16 : ℝ) ≤ D n := by exact_mod_cast hD16
  have hX0 : (0 : ℝ) < D n := by linarith
  have hle_D : (n : ℝ) ^ d / 2 ≤ D n := by linarith
  have hDn : D n ≤ n := by
    exact_mod_cast hfl.trans ((Real.rpow_le_rpow_of_exponent_le hN1 hd1).trans_eq (Real.rpow_one _))
  have hXη1 : 1 ≤ (D n : ℝ) ^ η := Real.one_le_rpow (by linarith) hη0.le
  have hgl : (D n : ℝ) ^ η ≤ g n := by rw [hg]; exact Nat.le_ceil _
  have hgu : (g n : ℝ) ≤ 2 * (D n : ℝ) ^ η := by
    have : (g n : ℝ) < (D n : ℝ) ^ η + 1 := by rw [hg]; exact Nat.ceil_lt_add_one (by positivity)
    linarith
  have hg1 : 1 ≤ g n := by exact_mod_cast hXη1.trans hgl
  have hg0 : (0 : ℝ) < g n := by exact_mod_cast hg1
  have hg_sqrt : (g n : ℝ) ≤ Real.sqrt (D n) := by
    have hhalf : (2 : ℝ) ^ (1 / (1 / 2 - η)) ≤ D n := by linarith [(le_max_right _ _).trans hn_d]
    have h2 : (2 : ℝ) ≤ (D n : ℝ) ^ (1 / 2 - η) := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / (1 / 2 - η))) ^ (1 / 2 - η) := by
            rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hτ0.ne', Real.rpow_one]
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hhalf hτ0.le
    rw [Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = η + (1 / 2 - η) by ring, Real.rpow_add hX0]
    nlinarith
  obtain ⟨hYl, hYu⟩ := pieceSize_bounds hD16 hg1 hg_sqrt hgl hgu
  generalize pieceSizeNat (D n) (g n) * Nat.sqrt (D n) = Dcn at hYl hYu ⊢
  have hXa : (D n : ℝ) ^ a ≤ (n : ℝ) ^ (d * a) := by
    rw [Real.rpow_mul hN0.le]; exact Real.rpow_le_rpow hX0.le hfl ha0.le
  have hXa' : (n : ℝ) ^ (d * a) / (2 : ℝ) ^ a ≤ (D n : ℝ) ^ a := by
    rw [Real.rpow_mul hN0.le, ← Real.div_rpow (by positivity) (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) hle_D ha0.le
  have hlow : ((1 / 8 : ℝ) / (2 : ℝ) ^ a) * (n : ℝ) ^ (d * a) ≤ Dcn := by
    calc ((1 / 8 : ℝ) / (2 : ℝ) ^ a) * (n : ℝ) ^ (d * a)
        = 1 / 8 * ((n : ℝ) ^ (d * a) / (2 : ℝ) ^ a) := by ring
      _ ≤ 1 / 8 * (D n : ℝ) ^ a := mul_le_mul_of_nonneg_left hXa' (by norm_num)
      _ ≤ Dcn := hYl
  have hup : (Dcn : ℝ) ≤ 2 * (n : ℝ) ^ (d * a) := hYu.trans (by gcongr)
  have hup' : 2 * (n : ℝ) ^ (d * a) ≤ (n : ℝ) ^ min ε 1 := by
    calc 2 * (n : ℝ) ^ (d * a) ≤ (n : ℝ) ^ (min ε 1 - d * a) * (n : ℝ) ^ (d * a) :=
          mul_le_mul_of_nonneg_right hn_a (by positivity)
      _ = (n : ℝ) ^ min ε 1 := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hlow0 : 0 < ((1 / 8 : ℝ) / (2 : ℝ) ^ a) * (n : ℝ) ^ (d * a) := by positivity
  have hY0 : (0 : ℝ) < Dcn := hlow0.trans_le hlow
  have fG : (g n : ℝ) ≤ 2 * (n : ℝ) ^ (d * η) := by
    have h1 := Real.rpow_le_rpow hX0.le hfl hη0.le
    rw [← Real.rpow_mul hN0.le] at h1; linarith
  have fGi : 1 / (g n : ℝ) ≤ 2 * (n : ℝ) ^ (-(d * η)) := by
    have h1 := Real.rpow_le_rpow (by positivity) hle_D hη0.le
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hN0.le] at h1
    have h2 : (2 : ℝ) ^ η ≤ 2 :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)).trans_eq (Real.rpow_one _)
    have h3 := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (d * η)) (by positivity) h2
    rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_div_iff₀ hg0 (by positivity)]; linarith
  have fW : (n : ℝ) ^ 2 / Real.sqrt (D n) ≤ 2 * (n : ℝ) ^ (2 + -(d / 2)) := by
    have hsq1 : (n : ℝ) ^ (d / 2) ≤ 2 * Real.sqrt (D n) := by
      rw [show (n : ℝ) ^ (d / 2) = Real.sqrt ((n : ℝ) ^ d) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; congr 1; ring, Real.sqrt_le_iff]
      exact ⟨by positivity, by rw [mul_pow, Real.sq_sqrt hX0.le]; linarith⟩
    have hinv : 1 / Real.sqrt (D n) ≤ 2 * (n : ℝ) ^ (-(d / 2)) := by
      rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_div_iff₀ (Real.sqrt_pos.2 hX0) (by positivity)]
      linarith
    rw [Real.rpow_add hN0, Real.rpow_two, div_eq_mul_one_div]
    exact (mul_le_mul_of_nonneg_left hinv (by positivity)).trans_eq (by ring)
  exact ⟨hn3, hD16, hDn, hg1, hg_sqrt, hfl, fG, fGi, fW,
    Nat.succ_le_of_lt (by exact_mod_cast hY0),
    (hup.trans hup').trans (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)),
    (hup.trans hup').trans ((Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)).trans_eq
      (Real.rpow_one _)),
    (Real.rpow_le_rpow_of_nonpos hlow0 hlow (by linarith)).trans_eq
      (by rw [Real.mul_rpow hc₀.le (by positivity), ← Real.rpow_mul hN0.le]),
    (Real.rpow_le_rpow hY0.le hup hq).trans_eq
      (by rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN0.le])⟩

private lemma log_add_one_pow_three_le {N τ : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ) :
    (Real.log N + 1) ^ 3 ≤ (3 / τ + 1) ^ 3 * N ^ τ := by
  have hN0 : 0 < N := by linarith
  have h3 : 0 < τ / 3 := by positivity
  have hlog := Real.log_le_rpow_div hN0.le h3
  have hone := Real.one_le_rpow hN h3.le
  have hle : Real.log N + 1 ≤ (3 / τ + 1) * N ^ (τ / 3) := by
    have : N ^ (τ / 3) / (τ / 3) = 3 / τ * N ^ (τ / 3) := by field_simp
    linarith
  calc (Real.log N + 1) ^ 3 ≤ ((3 / τ + 1) * N ^ (τ / 3)) ^ 3 :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hN]) hle 3
    _ = (3 / τ + 1) ^ 3 * N ^ τ := by
        rw [mul_pow, ← Real.rpow_natCast (N ^ (τ / 3)) 3, ← Real.rpow_mul hN0.le]
        congr 2; push_cast; ring

private lemma logb_two_seven_le : Real.logb 2 7 ≤ 2.81 := by
  refine (Real.logb_le_iff_le_rpow (by norm_num) (by norm_num) |>.2 ?_).trans
    (by norm_num : (250 : ℝ) / 89 ≤ 2.81)
  refine le_of_pow_le_pow_left₀ (n := 89) (by norm_num) (by positivity) ?_
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (250 / 89 : ℝ)) 89, ← Real.rpow_mul (by norm_num),
    show (250 / 89 : ℝ) * (89 : ℕ) = (250 : ℕ) by norm_num, Real.rpow_natCast]
  norm_num

private lemma prod5_le {N x₁ x₂ x₃ x₄ x₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ E : ℝ} (hN : 1 ≤ N)
    (h0₂ : 0 ≤ x₂) (h0₃ : 0 ≤ x₃) (h0₄ : 0 ≤ x₄) (h0₅ : 0 ≤ x₅)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) (hc₅ : 0 ≤ c₅)
    (h₁ : x₁ ≤ c₁ * N ^ e₁) (h₂ : x₂ ≤ c₂ * N ^ e₂) (h₃ : x₃ ≤ c₃ * N ^ e₃)
    (h₄ : x₄ ≤ c₄ * N ^ e₄) (h₅ : x₅ ≤ c₅ * N ^ e₅) (hE : e₁ + e₂ + e₃ + e₄ + e₅ ≤ E) :
    x₁ * x₂ * x₃ * x₄ * x₅ ≤ c₁ * c₂ * c₃ * c₄ * c₅ * N ^ E := by
  have hN0 : 0 < N := by linarith
  calc x₁ * x₂ * x₃ * x₄ * x₅
      ≤ c₁ * N ^ e₁ * (c₂ * N ^ e₂) * (c₃ * N ^ e₃) * (c₄ * N ^ e₄) * (c₅ * N ^ e₅) := by gcongr
    _ = c₁ * c₂ * c₃ * c₄ * c₅ * N ^ (e₁ + e₂ + e₃ + e₄ + e₅) := by
        simp only [Real.rpow_add hN0]; ring
    _ ≤ c₁ * c₂ * c₃ * c₄ * c₅ * N ^ E :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hE) (by positivity)

private lemma total_le {Tn N G Tdv pre wq rd sc pr bd C CL S R κ k1 k2 k3 k4 : ℝ}
    (h17 : Tn ≤ 4 * N * G * (Tdv + C * rd) + C * (sc + pr + bd))
    (hL : Tdv ≤ CL * (pre + wq)) (hB : 0 ≤ pre + wq) (hNG : 0 ≤ N * G) (hC : 0 ≤ C)
    (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2) (hk3 : 0 ≤ k3) (hk4 : 0 ≤ k4)
    (t1 : N * G * pre ≤ k1 * S) (t2 : N * G * wq ≤ k2 * S) (t3 : N * G * rd ≤ k3 * S)
    (t4 : sc ≤ κ * (k4 * S)) (t5 : pr ≤ S) (t6 : bd ≤ 2 * S) (hS : S ≤ R) (hκS : κ * S ≤ R) :
    Tn ≤ (4 * |CL| * k1 + 4 * |CL| * k2 + 4 * C * k3 + C * k4 + C + C * 2) * R := by
  have hTd := hL.trans (mul_le_mul_of_nonneg_right (le_abs_self CL) hB)
  have s0 : 4 * N * G * (Tdv + C * rd) ≤ 4 * N * G * (|CL| * (pre + wq) + C * rd) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have b1 := mul_le_mul_of_nonneg_left t1 (by positivity : 0 ≤ 4 * |CL|)
  have b2 := mul_le_mul_of_nonneg_left t2 (by positivity : 0 ≤ 4 * |CL|)
  have b3 := mul_le_mul_of_nonneg_left t3 (by positivity : 0 ≤ 4 * C)
  have b4 := mul_le_mul_of_nonneg_left t4 hC
  have b5 := mul_le_mul_of_nonneg_left t5 hC
  have b6 := mul_le_mul_of_nonneg_left t6 hC
  have r1 := mul_le_mul_of_nonneg_left hS
    (by positivity : 0 ≤ 4 * |CL| * k1 + 4 * |CL| * k2 + 4 * C * k3 + C + C * 2)
  have r2 := mul_le_mul_of_nonneg_left hκS (by positivity : 0 ≤ C * k4)
  linarith

theorem explicitFrom_mid (M : DetTimeModel) {d η ε γ q δ s : ℝ} {D g : ℕ → ℕ}
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hη0 : 0 < η) (hη1 : η < 1 / 2) (hγ : 0 ≤ γ) (hq : 0 ≤ q)
    (hsmall : 3 / 2 * d + δ ≤ 19 / 100)
    (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊)
    (hhost : HostBound M strassen D g (fun n => pieceSizeNat (D n) (g n) * Nat.sqrt (D n)))
    (hlop : LopClaim M ε γ q) (hthin : d * (1 - η) < ε)
    (hs1 : s ≤ d * η) (hs2 : s ≤ d * (γ * (1 - η) - η)) (hs3 : s ≤ d * (1 / 2 - q * (1 - η) - η))
    (hδ : δ < s) : ExplicitFrom M δ 1 := by
  obtain ⟨C, hC, hhost⟩ := hhost
  obtain ⟨CL, Td, hTd, hlop⟩ := hlop
  obtain ⟨T, hT, hhost⟩ := hhost Td hTd
  obtain ⟨n₀, K₁, K₂, hK₁, hK₂, hstep⟩ := exists_midStep hd0 hd1 hη0 hη1 hγ hq hthin hD hg
  have hτ : 0 < s - δ := sub_pos.2 hδ
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = (3 / (s - δ) + 1) ^ 3 := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  refine ⟨n₀, 4 * |CL| * (2 * K₁ * K') + 4 * |CL| * (4 * K₂ * K') + 4 * C * (4 * K')
    + C * (2 * K') + C + C * 2, T, hT, fun n κ u hn hκ hu => ?_⟩
  have P := hstep n hn
  have hn3 := P.hn3
  have h17 := hhost n κ u P.sixteen_le P.le_n P.one_le_g P.g_le_sqrt hκ hu
  dsimp only at h17
  generalize pieceSizeNat (D n) (g n) * Nat.sqrt (D n) = Dcn at P h17
  have hL := hlop n Dcn (queryCap n (D n)) (by omega) P.dc_one P.dc_eps
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hN0 : (0 : ℝ) < n := by linarith
  have hY1 : (1 : ℝ) ≤ Dcn := by exact_mod_cast P.dc_one
  have hY0 : (0 : ℝ) < Dcn := by linarith
  have hG0 : (0 : ℝ) ≤ g n := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ D n := Nat.cast_nonneg _
  have hlogn : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le hn3
  have hlogY0 : 0 ≤ Real.log Dcn := Real.log_nonneg hY1
  have hlogY : Real.log Dcn ≤ Real.log n := Real.log_le_log hY0 P.dc_n
  have hL1 : 1 ≤ Real.log n + 1 := by linarith
  have hL3 : (Real.log n + 1) ^ 3 ≤ K' * (n : ℝ) ^ (s - δ) := by
    rw [hK']; exact log_add_one_pow_three_le hN1 hτ
  have hlam2 : (Real.log Dcn + 1) ^ 2 ≤ K' * (n : ℝ) ^ (s - δ) :=
    ((pow_le_pow_left₀ (by linarith) (by linarith) 2).trans
      (pow_le_pow_right₀ hL1 (by norm_num))).trans hL3
  have hlam1 : Real.log Dcn + 1 ≤ K' * (n : ℝ) ^ (s - δ) :=
    ((by linarith : Real.log Dcn + 1 ≤ Real.log n + 1).trans
      (le_self_pow₀ hL1 (by norm_num))).trans hL3
  have hlam0 : (1 : ℝ) ≤ K' * (n : ℝ) ^ (s - δ) := (one_le_pow₀ hL1).trans hL3
  have hlamn : Real.log n ≤ K' * (n : ℝ) ^ (s - δ) :=
    ((by linarith : Real.log n ≤ Real.log n + 1).trans (le_self_pow₀ hL1 (by norm_num))).trans hL3
  have fN : (n : ℝ) ≤ 1 * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one, one_mul]
  have fN2 : (n : ℝ) ^ 2 ≤ 1 * (n : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two, one_mul]
  have fN3 : (n : ℝ) ^ 3 ≤ 1 * (n : ℝ) ^ (3 : ℝ) := by rw [one_mul, ← Real.rpow_natCast]; norm_num
  have f1 : (1 : ℝ) ≤ 1 * (n : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero, one_mul]
  have hw : (queryCap n (D n) : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt (D n) := Nat.floor_le (by positivity)
  have fX : (D n : ℝ) ≤ 1 * (n : ℝ) ^ d := by rw [one_mul]; exact P.D_le
  have fX32 : (D n : ℝ) ^ (3 / 2 : ℝ) ≤ 1 * (n : ℝ) ^ (d * (3 / 2)) := by
    rw [one_mul, Real.rpow_mul hN0.le]; exact Real.rpow_le_rpow hX0 P.D_le (by norm_num)
  have fMM : strassen n ≤ 1 * (n : ℝ) ^ (2.81 : ℝ) := by
    rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hN1 logb_two_seven_le
  have hdη : d * η ≤ d * (1 / 2) := mul_le_mul_of_nonneg_left hη1.le hd0.le
  have ha0 : 0 ≤ 1 - η := by linarith
  have hdqa : 0 ≤ d * (q * (1 - η)) := by positivity
  have t1 : (n : ℝ) * g n * preBound31 γ n Dcn ≤ 2 * K₁ * K' * (n : ℝ) ^ (3 - δ) := by
    rw [show (n : ℝ) * g n * preBound31 γ n Dcn =
      (n : ℝ) * g n * (n : ℝ) ^ 2 * (Dcn : ℝ) ^ (-γ) * (Real.log Dcn + 1) ^ 2 by
        rw [preBound31, Real.rpow_neg hY0.le]; ring]
    exact (prod5_le (E := 3 - δ) hN1 hG0 (by positivity) (by positivity) (by positivity)
      (by norm_num) (by norm_num) (by norm_num) hK₁ hK'0 fN P.g_le fN2 P.dc_neg hlam2
      (by linarith)).trans_eq (by ring)
  have t2 : (n : ℝ) * g n * ((queryCap n (D n) : ℝ) * queryBound31 q Dcn)
      ≤ 4 * K₂ * K' * (n : ℝ) ^ (3 - δ) := by
    rw [show (n : ℝ) * g n * ((queryCap n (D n) : ℝ) * queryBound31 q Dcn) =
      (n : ℝ) * g n * (queryCap n (D n) : ℝ) * (Dcn : ℝ) ^ q * (Real.log Dcn + 1) by
        rw [queryBound31]; ring]
    exact (prod5_le (E := 3 - δ) hN1 hG0 (by positivity) (by positivity) (by linarith)
      (by norm_num) (by norm_num) (by norm_num) hK₂ hK'0 fN P.g_le (hw.trans P.cap_le) P.dc_pos hlam1
      (by linarith)).trans_eq (by ring)
  have t3 : (n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) ≤ 4 * K' * (n : ℝ) ^ (3 - δ) := by
    rw [show (n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) =
      (n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) * 1 * 1 by ring]
    exact (prod5_le (E := 3 - δ) hN1 hG0 (by positivity) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK'0 fN P.g_le P.cap_le f1 hlam0
      (by linarith)).trans_eq (by ring)
  have t4 : termScans n (g n) κ ≤ κ * (2 * K' * (n : ℝ) ^ (3 - δ)) := by
    rw [show termScans n (g n) κ = κ * ((n : ℝ) ^ 3 * (1 / (g n : ℝ)) * 1 * 1 * Real.log n) by
      rw [termScans]; ring]
    exact mul_le_mul_of_nonneg_left ((prod5_le (E := 3 - δ) hN1 (by positivity) (by norm_num)
      (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK'0
      fN3 P.inv_g_le f1 f1 hlamn (by linarith)).trans_eq (by ring)) (by linarith)
  have t5 : termPrime strassen n (D n) ≤ (n : ℝ) ^ (3 - δ) := by
    rw [show termPrime strassen n (D n) = strassen n * (D n : ℝ) ^ (3 / 2 : ℝ) * 1 * 1 * 1 by
      rw [termPrime]; ring]
    exact (prod5_le (E := 3 - δ) hN1 (by positivity) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) fMM fX32 f1 f1 f1
      (by linarith)).trans_eq (by ring)
  have t6 : termBuild n (D n) (g n) ≤ 2 * (n : ℝ) ^ (3 - δ) := by
    rw [show termBuild n (D n) (g n) = (n : ℝ) ^ 2 * (D n : ℝ) * (g n : ℝ) * 1 * 1 by
      rw [termBuild]; ring]
    exact (prod5_le (E := 3 - δ) hN1 hX0 hG0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) fN2 fX P.g_le f1 f1
      (by linarith)).trans_eq (by ring)
  have hS0 : 0 ≤ (n : ℝ) ^ (3 - δ) := by positivity
  have hpre0 : 0 ≤ preBound31 γ n Dcn := by rw [preBound31]; positivity
  have hquery0 : 0 ≤ queryBound31 q Dcn := mul_nonneg (by positivity) (by linarith)
  have hS : (n : ℝ) ^ (3 - δ) ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1) := by
    rw [pow_one]
    exact (by ring : (n : ℝ) ^ (3 - δ) = 1 * ((n : ℝ) ^ (3 - δ) * 1)).trans_le
      (mul_le_mul hκ (mul_le_mul_of_nonneg_left hlogn hS0) (by positivity) (by linarith))
  have hκS : κ * (n : ℝ) ^ (3 - δ) ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1) := by
    rw [pow_one]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hS0 hlogn) (by linarith)
  exact total_le h17 hL (add_nonneg hpre0 (mul_nonneg (Nat.cast_nonneg _) hquery0))
    (mul_nonneg hN0.le hG0) hC (by positivity) (by positivity) (by positivity) (by positivity)
    t1 t2 t3 t4 t5 t6 hS hκS

end ImprovedExponents
