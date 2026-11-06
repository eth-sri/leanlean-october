module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Time

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The shared stage, in natural numbers -/

/-- `(L + 1)² ≤ 10^L`. -/
theorem succ_sq_le_ten_pow (L : ℕ) : (L + 1) ^ 2 ≤ 10 ^ L := by
  have hfour : (L + 1) ^ 2 ≤ 4 ^ L := by
    induction L with
    | zero => simp
    | succ L ih =>
      calc (L + 1 + 1) ^ 2 ≤ 4 * (L + 1) ^ 2 := by
            rw [show (L + 1 + 1) ^ 2 = L * L + 4 * L + 4 by ring,
              show 4 * (L + 1) ^ 2 = 4 * (L * L) + 8 * L + 4 by ring]
            omega
        _ ≤ 4 * 4 ^ L := Nat.mul_le_mul_left _ ih
        _ = 4 ^ (L + 1) := by ring
  exact hfour.trans (Nat.pow_le_pow_left (by norm_num) L)

/-- The facts about the sizes that the two estimates below use; T is `10^L` and S7 is `7^L`. -/
structure SizeFacts (L m K KK N0 D S7 T : ℕ) : Prop where
  sq : (L + 1) ^ 2 ≤ T
  KL : K * L ≤ T
  KND : K * N0 * D ≤ S7
  LS : L * S7 ≤ 2 * T
  ST : S7 ≤ T
  KK_le : KK ≤ K
  K_pos : 1 ≤ K
  N0_pos : 1 ≤ N0
  D_pos : 1 ≤ D
  L_pos : 1 ≤ L
  mL : m ≤ L

theorem sizeFacts (p : Sec2.Par) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    SizeFacts p.L p.m p.K p.KK p.N0 p.D p.S7 p.T :=
  ⟨succ_sq_le_ten_pow p.L, Theorem30.subsets p.L p.m, Theorem30.K_mul_N0_mul_D_le p.L p.m,
    Theorem30.form_array p.L, Nat.pow_le_pow_left (by norm_num) p.L, Nat.sqrt_le _,
    Nat.choose_pos hmL, Nat.one_le_pow _ _ (by norm_num), Nat.one_le_pow _ _ (by norm_num), hL1,
    hmL⟩

/-- The length of the shared block. -/
theorem sharedEnd_sub_le (p : Sec2.Par) (b0 : ℕ) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    p.sharedEnd b0 - b0 ≤ 190 * 10 ^ p.L + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * 10 ^ p.L) := by
  obtain ⟨sq, KL, KND, LS, ST, KKle, K1, N1, D1, L1, mL⟩ := sizeFacts p hL1 hmL
  have hLo : p.Lo ≤ p.L := Nat.sub_le _ _
  simp only [Sec2.Par.sharedEnd, Sec2.Par.aZS, Sec2.Par.aARR, Sec2.Par.aENCB, Sec2.Par.aENCA,
    Sec2.Par.aDIG4, Sec2.Par.aDIG3, Sec2.Par.aBLOCK, Sec2.Par.aBAND, Sec2.Par.aMASK, Sec2.Par.aPSI,
    Sec2.Par.aPHI, Sec2.Par.aPAS, Sec2.Par.aP10, Sec2.Par.aP7, Sec2.Par.aP4, Sec2.Par.aP3]
  change _ ≤ 190 * p.T + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * p.T)
  generalize p.T = T at *
  generalize p.S7 = S7 at *
  generalize p.K = K at *
  generalize p.KK = KK at *
  generalize p.N0 = N0 at *
  generalize p.D = D at *
  generalize p.nB = nB at *
  generalize p.Lo = Lo at *
  generalize p.N = N at *
  generalize p.L = L at *
  generalize p.m = m at *
  have : L + 1 ≤ T := (Nat.le_self_pow (by norm_num) _).trans sq
  have hDS : D ≤ S7 := le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos K1 N1)) KND
  have : KK * L ≤ K * L := Nat.mul_le_mul_right _ KKle
  have : N * Lo ≤ N * L := Nat.mul_le_mul_left _ hLo
  have : D * m ≤ L * S7 := (Nat.mul_le_mul hDS mL).trans (le_of_eq (Nat.mul_comm _ _))
  rw [Nat.mul_add_one N L]
  omega

/-! ## Within (8) -/

/-- The length of the block, split into the shared block, the scratch strings, and the tries with
their roots. -/
theorem top_sub_eq (p : Sec2.Par) (t b0 : ℕ) :
    top p t b0 - b0 = (p.sharedEnd b0 - b0) + (3 * p.L + p.m + 2)
      + (1 + p.nB * p.nB * (11 * (1 + p.L * (boxes p.L p.m t).card)) + p.nB * p.nB) := by
  have := base_le_sharedEnd p b0
  simp only [top, aTR, aROOTS, aFP, aSS, aBOX, aCUR, aWD, trieCap]
  omega

/-- **A query** takes `O(L ∑_{d ≤ t} α_d)` steps. -/
theorem exists_tQueryAt_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tQueryAt p.L p.m t : ℝ) ≤ C * costQuery p.L p.m t := by
  obtain ⟨C, hC, hcore⟩ := exists_tQueryCore_le
  refine ⟨C + 510, by positivity, fun p t h => ?_⟩
  have hcore := hcore p.L p.m t h.L_pos h.m_le h.t_le
  have := cast_L_le_costQuery p.L p.m t
  have : (1 : ℝ) ≤ p.L := by exact_mod_cast h.L_pos
  -- tQueryAt = 70 L + 440 + tQueryCore
  unfold tQueryAt tOutDigits
  push_cast
  linarith




/-- There are at most `11^L` cubes. -/
theorem card_boxes_le (L m t : ℕ) : (boxes L m t).card ≤ 11 ^ L := by
  have hsymbols : Fintype.card CubeSymbol = 11 := rfl
  calc (boxes L m t).card ≤ (univ : Finset (Cube L)).card := card_filter_le _ _
    _ = 11 ^ L := by rw [card_univ, Fintype.card_fun, hsymbols, Fintype.card_fin]

/-- The number of bands is at most `N + 1`. -/
theorem numBands_le (L m N : ℕ) (hmL : m ≤ L) : numBands L m N ≤ N + 1 := by
  have hband : 1 ≤ bandSize L m :=
    Nat.mul_pos (Nat.sqrt_pos.mpr (Nat.choose_pos hmL)) (Nat.one_le_pow _ _ (by norm_num))
  have : N ≤ bandSize L m * N := Nat.le_mul_of_pos_left _ hband
  refine Nat.div_le_of_le_mul ?_
  rw [Nat.mul_add_one]
  omega

/-- `N₀ ≤ N` under the hypotheses of Theorem 30. -/
theorem N0_le_N {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : N0 p.L p.m ≤ p.N := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (K p.L p.m : ℝ) :=
    Real.one_le_sqrt.2 (by exact_mod_cast Nat.choose_pos hmL)
  exact_mod_cast (le_mul_of_one_le_left (Nat.cast_nonneg _) hsqrt).trans h.N_ge

/-- Everything that depends on `L` is at most `B`; see `below` for `B = (N + 1)^5`. -/
structure Below (p : Sec2.Par) (t B : ℕ) : Prop where
  one : 1 ≤ B
  T : 10 ^ p.L ≤ B
  S7 : 7 ^ p.L ≤ B
  L1 : p.L + 1 ≤ B
  tenm : 10 ^ p.m ≤ B
  bx : (boxes p.L p.m t).card ≤ B
  nB : p.nB ≤ B
  N : p.N ≤ B

/-- "Since N ≥ N₀ = 3^{L-m} and L ≥ 10m, we have 10^L ≤ N^{5/2}": so all these quantities are at
most `(10^L)² ≤ N^5`. -/
theorem below {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : Below p t ((p.N + 1) ^ 5) := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have := Theorem30.ten_pow_le p.L p.m p.N h.L_ge (N0_le_N h)
  have : p.N ^ 5 ≤ (p.N + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have : 10 ^ p.L ≤ (10 ^ p.L) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hT : 10 ^ p.L ≤ (p.N + 1) ^ 5 := by omega
  have hN1 : p.N + 1 ≤ (p.N + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have hL1 : p.L + 1 ≤ (p.L + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have : 11 ^ p.L ≤ (10 ^ p.L) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) _
  exact ⟨by omega, hT, (Nat.pow_le_pow_left (by norm_num) _).trans hT,
    (hL1.trans (succ_sq_le_ten_pow p.L)).trans hT,
    (Nat.pow_le_pow_right (by norm_num) hmL).trans hT,
    (card_boxes_le _ _ _).trans (by omega), (numBands_le p.L p.m p.N hmL).trans hN1, by omega⟩

/-- The length of the block is at most `222 B⁴`. -/
theorem top_sub_le_pow {p : Sec2.Par} {t B : ℕ} (h : Hyp30 p t) (hB : Below p t B) (b0 : ℕ) :
    top p t b0 - b0 ≤ 222 * B ^ 4 := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hL1 : 1 ≤ p.L := by have := h.L_ge; have := h.m_pos; omega
  obtain ⟨hone, hT, -, hL, -, hbx, hnB, hN⟩ := hB
  have hshared := sharedEnd_sub_le p b0 hL1 hmL
  rw [top_sub_eq]
  generalize p.sharedEnd b0 - b0 = E at *
  generalize (boxes p.L p.m t).card = bx at *
  generalize p.nB = nB at *
  generalize 10 ^ p.L = T at *
  -- each product of two of the quantities is at most B², and so on
  have hNL : p.N * (p.L + 1) ≤ B * B := Nat.mul_le_mul hN hL
  have hnT : nB * T ≤ B * B := Nat.mul_le_mul hnB hT
  have hnn : nB * nB ≤ B * B := Nat.mul_le_mul hnB hnB
  have hLb : p.L * bx ≤ B * B := Nat.mul_le_mul (by omega) hbx
  have htries : nB * nB * (11 * (1 + p.L * bx)) ≤ B * B * (11 * (B + B * B)) :=
    Nat.mul_le_mul hnn (by omega)
  -- and every power of B up to the fourth is at most B⁴
  have hpow : ∀ j ≤ 4, B ^ j ≤ B ^ 4 := fun j hj => Nat.pow_le_pow_right hone hj
  have hB0 := hpow 0 (by norm_num)
  have hB1 := hpow 1 (by norm_num)
  have hB2 := hpow 2 (by norm_num)
  have hB3 := hpow 3 (by norm_num)
  rw [pow_zero] at hB0
  rw [pow_one] at hB1
  rw [show B ^ 2 = B * B by ring] at hB2
  rw [show B ^ 3 = B * B * B by ring] at hB3
  rw [show B * B * (11 * (B + B * B)) = 11 * (B * B * B) + 11 * B ^ 4 by ring] at htries
  omega

end Light.Sec4
