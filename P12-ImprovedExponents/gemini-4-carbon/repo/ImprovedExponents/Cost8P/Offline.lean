module

public import ThreeSumApsp.Programs.Sec4.Theorem30.TimeOfBlock
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.RealParameters
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ImprovedExponents.Pipeline.HostBound
public import ImprovedExponents.PrunedEncoding.Costs
public import ImprovedExponents.PrunedProgram.Pre.Defs
import all ThreeSumApsp.Programs.Sec4.Theorem30.Time

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Real Light Light.Sec4

def OfflineWithinT (t : ℕ → ℕ → ℕ → ℕ) (ε γ q : ℝ) : Prop :=
  ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
    (t N D₀ w : ℝ) + 400 ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)

theorem le_of_le_rpow {N D₀ : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : ε ≤ 1) (h : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) :
    D₀ ≤ N := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact_mod_cast h.trans ((Real.rpow_le_rpow_of_exponent_le hNR hε).trans_eq (Real.rpow_one _))

theorem rpow_le_sq {N D₀ : ℕ} {ε γ : ℝ} (hN : 1 ≤ N) (hγ : 0 ≤ γ) (hεγ : ε * γ ≤ 1)
    (h : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (D₀ : ℝ) ^ γ ≤ ((N : ℝ) ^ ε) ^ γ := Real.rpow_le_rpow (by positivity) h hγ
    _ = (N : ℝ) ^ (ε * γ) := by rw [← Real.rpow_mul (by positivity)]
    _ ≤ (N : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
    _ = (N : ℝ) ^ 2 := by norm_cast

theorem one_le_preBound31 {N D₀ : ℕ} {γ : ℝ} (hD : 1 ≤ D₀) (h : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2) :
    1 ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  unfold preBound31
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _), one_mul]
  exact h.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith)))

theorem le_preBound31 {N D₀ : ℕ} {γ γ' : ℝ} (hD : 1 ≤ D₀) (hγ : γ ≤ γ') :
    (N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ' ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  exact div_le_div₀ (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog (by linarith) 2) (by positivity))
    (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le hDR hγ)

theorem le_queryBound31 {D₀ : ℕ} {q q' : ℝ} (hD : 1 ≤ D₀) (hq : q' ≤ q) :
    (D₀ : ℝ) ^ q' * Real.log (D₀ : ℝ) ≤ queryBound31 q D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hDR hq) (by linarith) hlog (by positivity)

open private exists_tTile_le from ThreeSumApsp.Programs.Sec4.Theorem30.Time

private lemma pow_le_pow_sub {a b L m : ℕ} (hb : 0 < b) (hab : a ^ 10 ≤ b ^ 9) (hL : 10 * m ≤ L) :
    a ^ L ≤ b ^ (L - m) := by
  rw [← Nat.pow_le_pow_iff_left (by norm_num : (10 : ℕ) ≠ 0)]
  calc (a ^ L) ^ 10 = (a ^ 10) ^ L := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (b ^ 9) ^ L := Nat.pow_le_pow_left hab L
    _ = b ^ (9 * L) := by rw [← pow_mul]
    _ ≤ b ^ (10 * (L - m)) := Nat.pow_le_pow_right hb (by omega)
    _ = (b ^ (L - m)) ^ 10 := by rw [← pow_mul, mul_comm]

private lemma D_le_N0 {L m : ℕ} (hL : 10 * m ≤ L) : D m ≤ N0 L m :=
  (Nat.pow_le_pow_left (by norm_num : 4 ≤ 3 ^ 9) m).trans <|
    (pow_mul 3 9 m).symm.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

private lemma base_le_cost8P {L m : ℕ} (hL : 10 * m ≤ L) (t N : ℕ) :
    27 / 2 * ((N : ℝ) * (L : ℝ) * sqrtKN0 L m) ≤ cost8P L m t N := by
  have hfirst := cost8X_first_term_nonneg L m t N
  have hρ0 := rho_nonneg hL
  have hρ1 := sec4_rho_lt_one L m hL
  have hs := (sqrtKN0_pos (L := L) (m := m) (by omega)).le
  have hB : 0 ≤ (N : ℝ) * ((L : ℝ) * sqrtKN0 L m) := by positivity
  have hsec : 27 / 2 * ((N : ℝ) * (L : ℝ) * sqrtKN0 L m)
      ≤ (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m := by
    rw [encodingP_eq (by omega), le_div_iff₀ (sub_pos.2 hρ1)]; nlinarith
  unfold cost8P; linarith

private lemma one_le_sqrtKN0 {L m : ℕ} (hmL : m ≤ L) : 1 ≤ sqrtKN0 L m :=
  one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.2 (by exact_mod_cast Nat.choose_pos hmL))
    (by exact_mod_cast N0_pos L m)

private lemma N0_le_sqrtKN0 {L m : ℕ} (hmL : m ≤ L) : (N0 L m : ℝ) ≤ sqrtKN0 L m :=
  le_mul_of_one_le_left (Nat.cast_nonneg _) (Real.one_le_sqrt.2 (by exact_mod_cast Nat.choose_pos hmL))

theorem exists_tPreCore_leP (c : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tPreCoreP c p t : ℝ) ≤ C * cost8P p.L p.m t p.N := by
  obtain ⟨ct, hct⟩ := exists_tTile_le
  refine ⟨c * (52 * (2 / 27) + 2) + (ct * 8 + 30) + 300, by positivity, fun p t h => ?_⟩
  have hL := h.L_ge; have hm := h.m_pos; have hL1 := h.L_pos
  have hs1 := one_le_sqrtKN0 h.m_le
  have hN : 1 ≤ p.N := by exact_mod_cast hs1.trans h.N_ge
  have hbase := base_le_cost8P hL t p.N
  have h1cost : 1 ≤ cost8P p.L p.m t p.N := by
    have : (1 : ℝ) ≤ (p.N : ℝ) * (p.L : ℝ) * sqrtKN0 p.L p.m :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (hs1.trans h.N_ge) (by exact_mod_cast hL1)) hs1
    linarith
  -- Tables <= 52 * N * L * N0
  have hKn : p.K ≤ N0 p.L p.m :=
    (Nat.choose_le_two_pow p.L p.m).trans (pow_le_pow_sub (by norm_num) (by norm_num) hL)
  have hDn : p.D ≤ N0 p.L p.m := D_le_N0 hL
  have hLn : p.L ≤ 10 * N0 p.L p.m :=
    (by omega : p.L ≤ 10 * (p.L - p.m)).trans (Nat.mul_le_mul_left _ (Nat.lt_pow_self (by norm_num)).le)
  have htab_nat : (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1)
      + (p.N + 1) * (p.Lo + 1) + (p.D + 1) * (p.m + 1) ≤ 52 * (p.N * p.L * N0 p.L p.m) := by
    have hsqrt := Nat.sqrt_le_self p.K
    have hKK : p.KK ≤ p.K := Nat.sqrt_le _
    have hLo : p.Lo ≤ p.L := Nat.sub_le _ _
    have hn1 : 1 ≤ N0 p.L p.m := N0_pos p.L p.m
    have t1 : (p.L + 1) ^ 2 ≤ 40 * (p.N * p.L * N0 p.L p.m) :=
      (Nat.pow_le_pow_left (by omega : p.L + 1 ≤ 2 * p.L) 2).trans <|
        (by ring : _ = 4 * (p.L * p.L)).trans_le <|
        (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left p.L hLn)).trans <|
        (by ring : _ = 40 * (1 * p.L * N0 p.L p.m)).trans_le (by gcongr)
    have t2 : Nat.sqrt p.K + 1 ≤ 2 * (p.N * p.L * N0 p.L p.m) :=
      (by omega : Nat.sqrt p.K + 1 ≤ 2 * (1 * 1 * N0 p.L p.m)).trans (by gcongr)
    have t3 : (p.KK + 1) * (p.L + 1) ≤ 4 * (p.N * p.L * N0 p.L p.m) :=
      (Nat.mul_le_mul (by omega : p.KK + 1 ≤ 2 * N0 p.L p.m) (by omega : p.L + 1 ≤ 2 * p.L)).trans <|
        (by ring : _ = 4 * (1 * p.L * N0 p.L p.m)).trans_le (by gcongr)
    have t4 : (p.N + 1) * (p.Lo + 1) ≤ 4 * (p.N * p.L * N0 p.L p.m) :=
      (Nat.mul_le_mul (by omega : p.N + 1 ≤ 2 * p.N) (by omega : p.Lo + 1 ≤ 2 * p.L)).trans <|
        (by ring : _ = 4 * (p.N * p.L * 1)).trans_le (by gcongr)
    have t5 : (p.D + 1) * (p.m + 1) ≤ 2 * (p.N * p.L * N0 p.L p.m) :=
      (Nat.mul_le_mul (by omega : p.D + 1 ≤ 2 * N0 p.L p.m) (by omega : p.m + 1 ≤ p.L)).trans <|
        (by ring : _ = 2 * (1 * p.L * N0 p.L p.m)).trans_le (by gcongr)
    omega
  have htab : (((p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1)
        + (p.N + 1) * (p.Lo + 1) + (p.D + 1) * (p.m + 1) : ℕ) : ℝ)
      ≤ 52 * (2 / 27) * cost8P p.L p.m t p.N := by
    have hr : (((p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1)
        + (p.N + 1) * (p.Lo + 1) + (p.D + 1) * (p.m + 1) : ℕ) : ℝ)
        ≤ 52 * ((p.N : ℝ) * (p.L : ℝ) * N0 p.L p.m) := by exact_mod_cast htab_nat
    have := N0_le_sqrtKN0 h.m_le
    linarith [show 52 * ((p.N : ℝ) * p.L * N0 p.L p.m) ≤ 52 * ((p.N : ℝ) * p.L * sqrtKN0 p.L p.m) by gcongr]
  -- Bands <= 2 * cost8P
  have hρ := sec4_rho_lt_one p.L p.m hL
  have hρ0 := rho_nonneg hL
  have hMρ : (M p.L p.m : ℝ) ≤ (M p.L p.m : ℝ) / (1 - rho p.L p.m) :=
    le_div_self (Nat.cast_nonneg _) (sub_pos.2 hρ) (by linarith)
  have hMρ0 : 0 ≤ (M p.L p.m : ℝ) / (1 - rho p.L p.m) := (Nat.cast_nonneg _).trans hMρ
  have h7M : ((7 : ℕ) : ℝ) ^ p.L ≤ M p.L p.m := by
    have h7nat : 7 ^ p.L ≤ M p.L p.m :=
      (pow_le_pow_sub (a := 7) (b := 9) (by norm_num) (by norm_num) hL).trans <|
        (show 9 ^ (p.L - p.m) = N0 p.L p.m ^ 2 by
          change (3 ^ 2) ^ _ = (3 ^ _) ^ 2; rw [← pow_mul, ← pow_mul, mul_comm]).trans_le
          (Nat.le_mul_of_pos_left _ (Nat.choose_pos h.m_le))
    exact_mod_cast h7nat
  have hbshape : Sec2.bandArrayShape p ≤ 5 * (p.L * 7 ^ p.L) := by
    have hent : p.KK * p.N0 * p.D ≤ 7 ^ p.L :=
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sqrt_le p.K))).trans
        (Theorem30.K_mul_N0_mul_D_le p.L p.m)
    have hS1 : 1 ≤ 7 ^ p.L := Nat.one_le_pow _ _ (by norm_num)
    change 7 ^ p.L + (p.KK * p.N0 * p.D + 1) * (p.L + 1) ≤ _
    have : (p.KK * p.N0 * p.D + 1) * (p.L + 1) ≤ (7 ^ p.L + 1) * (p.L + 1) := by gcongr
    nlinarith
  have hwork : ((encWorkP p.L p.m + Sec2.bandArrayShape p : ℕ) : ℝ)
      ≤ 10 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))) := by
    have henc : (encWorkP p.L p.m : ℝ) ≤ 9 / 2 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))) := by
      have h1 := encWorkP_le_M_div hL; rw [mul_div_assoc] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hMρ0 (by exact_mod_cast hL1)) (by norm_num))
    have hb1 : (Sec2.bandArrayShape p : ℝ) ≤ 5 * ((p.L : ℝ) * (7 : ℝ) ^ p.L) := by exact_mod_cast hbshape
    have hb2 : 5 * ((p.L : ℝ) * (7 : ℝ) ^ p.L) ≤ 5 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))) := by
      gcongr; exact_mod_cast h7M.trans hMρ
    push_cast; linarith
  have hbands : ((p.nB * (encWorkP p.L p.m + Sec2.bandArrayShape p) : ℕ) : ℝ) ≤ 2 * cost8P p.L p.m t p.N := by
    have hnB : (p.nB : ℝ) ≤ 2 * (p.N : ℝ) / sqrtKN0 p.L p.m := by
      have := Theorem30.bands hm hL h.N_ge
      change (2 * numBands p.L p.m p.N : ℝ) ≤ 4 * (p.N : ℝ) / sqrtKN0 p.L p.m at this
      have : 4 * (p.N : ℝ) / sqrtKN0 p.L p.m = 2 * (2 * p.N / sqrtKN0 p.L p.m) := by ring
      change (numBands p.L p.m p.N : ℝ) ≤ _; linarith
    have hprod := mul_le_mul hnB hwork (Nat.cast_nonneg _) (by positivity)
    have hx : 0 ≤ (p.N : ℝ) * p.L * ((M p.L p.m : ℝ) / (1 - rho p.L p.m)) / sqrtKN0 p.L p.m := by positivity
    have hfirst := cost8X_first_term_nonneg p.L p.m t p.N
    rw [Nat.cast_mul]; unfold cost8P
    have heq1 : (2 * (p.N : ℝ) / sqrtKN0 p.L p.m) * (10 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))))
        = 20 * ((p.N : ℝ) * p.L * ((M p.L p.m : ℝ) / (1 - rho p.L p.m)) / sqrtKN0 p.L p.m) := by ring
    have heq2 : 2 * ((p.N : ℝ) * p.L * (27 / 2 * (M p.L p.m : ℝ) / (1 - rho p.L p.m)) / sqrtKN0 p.L p.m)
        = 27 * ((p.N : ℝ) * p.L * ((M p.L p.m : ℝ) / (1 - rho p.L p.m)) / sqrtKN0 p.L p.m) := by ring
    linarith
  have hshared : (Sec2.sharedShapeP p : ℝ) ≤ (52 * (2 / 27) + 2) * cost8P p.L p.m t p.N := by
    unfold Sec2.sharedShapeP; push_cast at htab hbands ⊢; linarith
  -- AllTiles <= (ct * 8 + 30) * cost8P
  have htiles : (tAllTiles p.L p.m t p.nB : ℝ) ≤ (ct * 8 + 30) * cost8P p.L p.m t p.N := by
    have hnat : tAllTiles p.L p.m t p.nB ≤ ct * (p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) + 30 := by
      have htile := hct p.L p.m t hL1 h.m_le
      have hn : p.nB ≤ p.nB ^ 2 := Nat.le_self_pow (by norm_num) _
      calc tAllTiles p.L p.m t p.nB = p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB * 40 + 30 := by simp [tAllTiles]; ring
        _ ≤ p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB ^ 2 * 40 + 30 := by gcongr
        _ = p.nB ^ 2 * (tTile p.L p.m t + 120) + 30 := by ring
        _ ≤ p.nB ^ 2 * (ct * (p.L * (boxes p.L p.m t).card)) + 30 := by gcongr
        _ = _ := by ring
    have hbx := boxes_costX hm hL h.t_le h.N_ge
    have hsec : 0 ≤ (p.N : ℝ) * p.L * (27 / 2 * (M p.L p.m : ℝ) / (1 - rho p.L p.m)) / sqrtKN0 p.L p.m :=
      div_nonneg (mul_nonneg (by positivity) (div_nonneg (by positivity) (sub_pos.2 hρ).le)) (by positivity)
    have hbx' : (((p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) : ℕ) : ℝ) ≤ 8 * cost8P p.L p.m t p.N := by
      push_cast; change (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * _) ≤ _
      unfold cost8P; linarith
    have hr : (tAllTiles p.L p.m t p.nB : ℝ) ≤ (ct : ℝ) * (((p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) : ℕ) : ℝ) + 30 := by
      exact_mod_cast hnat
    nlinarith [Nat.cast_nonneg (α := ℝ) ct]
  simp only [tPreCoreP]; push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) c]

theorem offlineWithinP (c₀ : ℕ) {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a)
    (hp : 1 ≤ p) (hθ : 10 * p < 9 * q) {γ ε : ℝ} (hγ0 : 0 < γ) (hε0 : 0 < ε)
    (hγ : γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q)) (hε : ε < RcP ((a : ℝ) / b) γ) :
    ∃ m₁ : ℕ, ∀ (m₀ : ℕ) (hm₀ : 1 ≤ m₀), m₁ ≤ m₀ →
      OfflineWithinT (tOffline32P c₀ ⟨a, b, p, q, m₀, hb, hq, hc, hp, hθ, hm₀⟩)
        ε γ (qOf ((p : ℝ) / q)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcR : (10 : ℝ) < (a : ℝ) / b := (lt_div_iff₀ hbR).2 (by exact_mod_cast hc)
  have hθ0 : (0 : ℝ) < (p : ℝ) / q := div_pos (by exact_mod_cast hp) hqR
  have hθ1 : (p : ℝ) / q < 0.9 := (div_lt_iff₀ hqR).2 (by linarith [show (10 : ℝ) * p < 9 * q by exact_mod_cast hθ])
  obtain ⟨C, m₁, hC, hcost⟩ := costsP hcR hθ0 hθ1 hγ0.le hγ hε0 hε
  have hA0 := basePruned_pos (by linarith : 1 < (a : ℝ) / b)
  have hden := thinR_den_pos hA0 hγ0.le
  have hε1 : ε ≤ 1 := by
    refine hε.le.trans ((div_le_one hden).2 ?_)
    have hH := entropy_nonneg (by positivity : 0 ≤ 1 / ((a : ℝ) / b)) ((div_le_one (by positivity)).2 (by linarith))
    have h43 : log 4 ≤ 9 * log 3 := by
      have := log_le_log (by norm_num) (by norm_num : (4 : ℝ) ≤ 3 ^ 9)
      rw [log_pow] at this; push_cast at this; exact this
    have : 0 ≤ γ * log 4 := mul_nonneg hγ0.le log_four_pos.le
    have : 0 < log 3 := log_pos (by norm_num)
    unfold basePruned; nlinarith
  have hεγ : ε * γ ≤ 1 := by
    have : RcP ((a : ℝ) / b) γ * γ ≤ 1 := by unfold RcP thinR; rw [div_mul_eq_mul_div, div_le_one hden]; linarith
    nlinarith
  obtain ⟨Cp, hCp0, hCp⟩ := exists_tPreCore_leP c₀
  refine ⟨m₁, fun m₀ hm₀ hm₁ => ?_⟩
  let G : RatParams := ⟨a, b, p, q, m₀, hb, hq, hc, hp, hθ, hm₀⟩
  obtain ⟨k, hk⟩ := exists_tPre31_le_setup G
  obtain ⟨Aq, hAq0, hAq⟩ := exists_tQuery31_le G hC
  set K : ℝ := k * 4 + Cp
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨Ap, hAp0, hAp⟩ := exists_le_of_small_of_large G hC
    (S := ((20 * G.m₀ + 50 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨(Ap + 420) + (Aq + 30), fun N D₀ w hN hD hDN => ?_⟩
  have htp1 : 1 ≤ preBound31 γ N D₀ := one_le_preBound31 hD (rpow_le_sq hN hγ0.le hεγ hDN)
  have htq1 : 1 ≤ queryBound31 (qOf ((p : ℝ) / q)) D₀ := one_le_queryBound31 hD (qOf_nonneg _ hθ0 hθ1)
  have hDN_le := le_of_le_rpow hN hε1 hDN
  have habove (hm : G.m₀ ≤ logFour D₀) : G.Hyp N D₀ ∧
      cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N ≤ C * preBound31 γ N D₀ ∧
      G.queryCost D₀ ≤ C * queryBound31 (qOf ((p : ℝ) / q)) D₀ := by
    have hm_pos : 1 ≤ logFour D₀ := hm₀.trans hm
    obtain ⟨hfit, hpre, hq'⟩ := hcost D₀ N (logFour D₀) (two_le_of_clog hm_pos) hDN
      (ceil_logb_four D₀).symm (hm₁.trans hm)
    rw [levelsOf_div a _ hb] at hfit hpre hq'
    rw [switchOf_div p _ hq] at hpre hq'
    exact ⟨⟨hm_pos, RatParams.ten_le_L _ _, RatParams.t_le _ _, hfit⟩,
      hpre.trans (mul_le_mul_of_nonneg_left (le_preBound31 hD le_rfl) hC),
      hq'.trans (mul_le_mul_of_nonneg_left (le_queryBound31 hD le_rfl) hC)⟩
  have hpre_le : (tPre31P c₀ G N D₀ : ℝ) ≤ Ap * preBound31 γ N D₀ := by
    refine hAp D₀ (cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N)
      (preBound31 γ N D₀) (tPre31P c₀ G N D₀ : ℝ)
      htp1 (fun hm => (habove hm).2.1) (fun hm => ?_) fun hm => ?_
    · exact_mod_cast (show tPre31P c₀ G N D₀ ≤ 20 * G.m₀ + 50 by
        unfold tPre31P tLog4; rw [ite_eq_left hm]; omega)
    · have hh := (habove hm).1
      have hcore : (tPreCoreP c₀ (parOf G N D₀) (switchOf31 G D₀) : ℝ)
          ≤ Cp * cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N :=
        hCp (parOf G N D₀) (switchOf31 G D₀) hh
      have hsetup : tPre31P c₀ G N D₀ ≤ k * (G.L (logFour D₀) + 1 + N * 4 ^ logFour D₀ + N)
          + tPreCoreP c₀ (parOf G N D₀) (switchOf31 G D₀) := by
        have := hk c₀ N D₀ hm
        have hdiff : tPre31P c₀ G N D₀ + tPreCore c₀ (parOf G N D₀) (switchOf31 G D₀)
            = tPre31 c₀ G N D₀ + tPreCoreP c₀ (parOf G N D₀) (switchOf31 G D₀) := by
          unfold tPre31P tPre31; rw [ite_eq_right (not_lt.2 hm), ite_eq_right (not_lt.2 hm)]; ring
        omega
      have hsetupR : (tPre31P c₀ G N D₀ : ℝ) ≤ k * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
          + tPreCoreP c₀ (parOf G N D₀) (switchOf31 G D₀) := by exact_mod_cast hsetup
      have hbase : 27 / 2 * ((N : ℝ) * G.L (logFour D₀) * sqrtKN0 (G.L (logFour D₀)) (logFour D₀))
          ≤ cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N :=
        base_le_cost8P hh.L_ge (switchOf31 G D₀) N
      have hs1 : 1 ≤ sqrtKN0 (G.L (logFour D₀)) (logFour D₀) := one_le_sqrtKN0 hh.m_le
      have hL1 : (1 : ℝ) ≤ G.L (logFour D₀) := by exact_mod_cast hh.L_pos
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hpos_base : 0 ≤ (N : ℝ) * G.L (logFour D₀) * sqrtKN0 (G.L (logFour D₀)) (logFour D₀) := by
        positivity
      have hNL : (N : ℝ) * (G.L (logFour D₀) + 1) ≤ cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N := by
        have : (N : ℝ) * (G.L (logFour D₀) + 1) ≤ 2 * ((N : ℝ) * G.L (logFour D₀) * sqrtKN0 _ _) :=
          (by nlinarith : (N : ℝ) * (G.L (logFour D₀) + 1) ≤ 2 * ((N : ℝ) * G.L (logFour D₀))).trans
            (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hs1) (by norm_num))
        linarith
      have hNF : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N := by
        have hD0 : (4 : ℝ) ^ logFour D₀ ≤ sqrtKN0 (G.L (logFour D₀)) (logFour D₀) := by
          have hd : (D (logFour D₀) : ℝ) ≤ sqrtKN0 (G.L (logFour D₀)) (logFour D₀) :=
            (Nat.cast_le.mpr (D_le_N0 hh.L_ge)).trans (N0_le_sqrtKN0 hh.m_le)
          simpa [D] using hd
        have h1 : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ (N : ℝ) * G.L (logFour D₀) * sqrtKN0 (G.L (logFour D₀)) (logFour D₀) := by
          calc (N : ℝ) * (4 : ℝ) ^ logFour D₀
              ≤ (N : ℝ) * sqrtKN0 (G.L (logFour D₀)) (logFour D₀) := by gcongr
            _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
                          (le_mul_of_one_le_left (by positivity) hL1) (Nat.cast_nonneg _)
        linarith
      have hL_le : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * (G.L (logFour D₀) + 1) :=
        le_mul_of_one_le_left (by positivity) hN1
      have hN_le : (N : ℝ) ≤ (N : ℝ) * (G.L (logFour D₀) + 1) :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
      have hsum := mul_le_mul_of_nonneg_left
        (by linarith : (G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N
          ≤ 4 * cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N) (Nat.cast_nonneg (α := ℝ) k)
      have : (0 : ℝ) ≤ ((20 * G.m₀ + 50 : ℕ) : ℝ) := by positivity
      unfold K; linarith
  have hq_le : (tQuery31 G D₀ : ℝ) ≤ Aq * queryBound31 (qOf ((p : ℝ) / q)) D₀ :=
    hAq (N := N) htq1 fun hm => ⟨(habove hm).1, (habove hm).2.2⟩
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have htime : (tOffline32P c₀ G N D₀ w : ℝ)
      = (tPre31P c₀ G N D₀ : ℝ) + w * ((tQuery31 G D₀ : ℝ) + 30) + 20 := by
    simp only [tOffline32P]; push_cast; ring
  have h2 := (mul_le_mul_of_nonneg_left (by linarith : (tQuery31 G D₀ : ℝ) + 30 ≤ (Aq + 30) * _) hw0).trans_eq
    (by ring : (w : ℝ) * ((Aq + 30) * queryBound31 (qOf ((p : ℝ) / q)) D₀)
      = (Aq + 30) * (w * queryBound31 (qOf ((p : ℝ) / q)) D₀))
  have hc1 : 0 ≤ (Ap + 420) * ((w : ℝ) * queryBound31 (qOf ((p : ℝ) / q)) D₀) := by positivity
  have hc2 : 0 ≤ (Aq + 30) * preBound31 γ N D₀ := by positivity
  rw [htime]; linarith

end ImprovedExponents
