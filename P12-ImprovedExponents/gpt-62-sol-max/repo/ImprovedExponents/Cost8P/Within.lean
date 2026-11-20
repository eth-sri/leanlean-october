module

public import ThreeSumApsp.Programs.Sec4.Theorem30.TimeOfBlock
public import ImprovedExponents.Cost8X.Defs
public import ImprovedExponents.PrunedEncoding.Costs
public import ImprovedExponents.PrunedProgram.Pre.Defs
import all ThreeSumApsp.Programs.Sec4.Theorem30.Time

@[expose] public section

/-!
# The pruned preprocessing of Theorem 30 runs within `cost8P`

`ImprovedExponents.Cost8X.Within` shows that upstream's preprocessing of Theorem 30 takes at most
a constant times `cost8X`, the expression (8) with the exact tail of the leaf counts. This file
repeats that analysis for the pruned preprocessing, whose time function `tPreCoreP` has the shape
`sharedShapeP` of the pruned shared stage: the work `encWorkP L m` of the pruned encoder takes the
place of the `10^L` cells of a full encoding. The cost is `cost8P`, whose second summand

  `N L (27/2) M/(1 - ρ)/(√K N₀)`

replaces the `N 10^L/(√K N₀)` of `cost8X`: `Within8P`, and `exists_tPreCore_leP`.

`cost8P` has no standalone `10^L` term, so the small summands of the shared stage (the tables, the
list of subsets, the directory, the digit tables) cannot be absorbed into one as upstream does
(`sharedShape_le`). They are bounded by `N L √K N₀`, which is at most `2/27` of the second
summand (`base_le_cost8P`): `K ≤ N₀`, `D ≤ N₀`, `L ≤ 10 N₀` for `10 m ≤ L` (`K_le_N0`, `D_le_N0`,
`L_le_ten_mul_N0`). The work of the pruned encoder is at most `(9/2) M/(1 - ρ)`
(`encWorkP_le_M_div`), and the input array of a band takes `O(L 7^L)` with `7^L ≤ 9^{L-m} ≤ M`
(`seven_pow_le_M`), so that the bands cost `O(N L M/((1 - ρ) √K N₀))`, the second summand. The
tries of all tiles are as in `Cost8X.Within` (`boxes_costX`, upstream's private
`exists_tTile_le`).

The statements and proofs are adapted from upstream
`ThreeSumApsp/Programs/Sec4/Theorem30/Time.lean` and `TimeOfBlock.lean` (Apache-2.0) and from
`ImprovedExponents/Cost8X/Within.lean`.
-/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4

open private exists_tTile_le from ThreeSumApsp.Programs.Sec4.Theorem30.Time

/-! ### Powers for `10 m ≤ L` -/

/-- For `a^10 ≤ b^9` and `10 m ≤ L`: `a^L ≤ b^{L-m}`, because `10 (L - m) ≥ 9 L`. -/
theorem pow_le_pow_sub_of_ten_mul_le {a b L m : ℕ} (hb : 0 < b) (hab : a ^ 10 ≤ b ^ 9)
    (hL : 10 * m ≤ L) : a ^ L ≤ b ^ (L - m) := by
  rw [← Nat.pow_le_pow_iff_left (by norm_num : (10 : ℕ) ≠ 0)]
  calc (a ^ L) ^ 10 = (a ^ 10) ^ L := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (b ^ 9) ^ L := Nat.pow_le_pow_left hab L
    _ = b ^ (9 * L) := by rw [← pow_mul]
    _ ≤ b ^ (10 * (L - m)) := Nat.pow_le_pow_right hb (by omega)
    _ = (b ^ (L - m)) ^ 10 := by rw [← pow_mul, mul_comm]

/-- `K = binom(L, m) ≤ 2^L ≤ 3^{L-m} = N₀` for `10 m ≤ L`. -/
theorem K_le_N0 {L m : ℕ} (hL : 10 * m ≤ L) : K L m ≤ N0 L m :=
  (Nat.choose_le_two_pow L m).trans (pow_le_pow_sub_of_ten_mul_le (by norm_num) (by norm_num) hL)

/-- `D = 4^m ≤ 3^{9m} ≤ 3^{L-m} = N₀` for `10 m ≤ L`. -/
theorem D_le_N0 {L m : ℕ} (hL : 10 * m ≤ L) : D m ≤ N0 L m :=
  calc D m = 4 ^ m := rfl
    _ ≤ (3 ^ 9) ^ m := Nat.pow_le_pow_left (by norm_num) m
    _ = 3 ^ (9 * m) := by rw [← pow_mul]
    _ ≤ 3 ^ (L - m) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `L ≤ 10 (L - m) ≤ 10 N₀` for `10 m ≤ L`. -/
theorem L_le_ten_mul_N0 {L m : ℕ} (hL : 10 * m ≤ L) : L ≤ 10 * N0 L m :=
  calc L ≤ 10 * (L - m) := by omega
    _ ≤ 10 * 3 ^ (L - m) := Nat.mul_le_mul_left _ (Nat.lt_pow_self (by norm_num)).le

/-- `7^L ≤ 9^{L-m} = N₀² ≤ K N₀² = M` for `10 m ≤ L`. -/
theorem seven_pow_le_M {L m : ℕ} (hL : 10 * m ≤ L) : 7 ^ L ≤ M L m :=
  calc 7 ^ L ≤ 9 ^ (L - m) := pow_le_pow_sub_of_ten_mul_le (by norm_num) (by norm_num) hL
    _ = N0 L m ^ 2 := by
        change (3 ^ 2) ^ (L - m) = (3 ^ (L - m)) ^ 2
        rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ K L m * N0 L m ^ 2 := Nat.le_mul_of_pos_left _ (Nat.choose_pos (by omega))

/-! ### The second summand of `cost8P` -/

/-- `N₀ ≤ √K N₀`. -/
theorem N0_le_sqrtKN0 {L m : ℕ} (hmL : m ≤ L) : (N0 L m : ℝ) ≤ sqrtKN0 L m :=
  le_mul_of_one_le_left (Nat.cast_nonneg _) (Real.one_le_sqrt.2 (by exact_mod_cast Nat.choose_pos hmL))

/-- `√K N₀ ≥ N₀ ≥ 1`. -/
theorem one_le_sqrtKN0 {L m : ℕ} (hmL : m ≤ L) : 1 ≤ sqrtKN0 L m :=
  (Nat.one_le_cast.2 (N0_pos L m)).trans (N0_le_sqrtKN0 hmL)

/-- The denominator of the encoding cost is positive and at most one. -/
private theorem le_div_one_sub_rho {L m : ℕ} (hL : 10 * m ≤ L) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ x / (1 - rho L m) :=
  le_div_self hx (sub_pos.2 (sec4_rho_lt_one L m hL)) (by linarith [rho_nonneg hL])

/-- The preprocessing cost covers `2 N L √K N₀`. -/
theorem base_le_cost8P {L m : ℕ} (hL : 10 * m ≤ L) (t N : ℕ) :
    2 * ((N : ℝ) * ((L : ℝ) * sqrtKN0 L m)) ≤ cost8P L m t N := by
  have hs := (one_le_sqrtKN0 (show m ≤ L by omega)).trans' zero_le_one
  have h := le_div_one_sub_rho hL (show 0 ≤ 27 / 2 * ((N : ℝ) * ((L : ℝ) * sqrtKN0 L m)) by positivity)
  unfold cost8P
  linarith [cost8X_first_term_nonneg L m t N,
    show 0 ≤ (N : ℝ) * ((L : ℝ) * sqrtKN0 L m) by positivity]

/-- `cost8P` is at least 1 on its domain. -/
theorem one_le_cost8P {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : 1 ≤ cost8P p.L p.m t p.N := by
  have hs := one_le_sqrtKN0 h.m_le
  have hL : (1 : ℝ) ≤ p.L := Nat.one_le_cast.2 h.L_pos
  have hbase : 0 ≤ (p.N : ℝ) * ((p.L : ℝ) * sqrtKN0 p.L p.m) := by positivity
  calc 1 = (1 : ℝ) * (1 * 1) := by ring
    _ ≤ (p.N : ℝ) * ((p.L : ℝ) * sqrtKN0 p.L p.m) := by gcongr; exact hs.trans h.N_ge
    _ ≤ _ := by linarith [base_le_cost8P h.L_ge t p.N]

/-! ### `Within8P` -/

/-- `f = O(cost8P)`: at most a constant times `cost8P`, for all parameters that satisfy the
hypotheses of Theorem 30. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X)
def Within8P (f : Sec2.Par → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, Hyp30 p t → (f p t : ℝ) ≤ C * cost8P p.L p.m t p.N

namespace Within8P

variable {f g : Sec2.Par → ℕ → ℕ}

/-- A smaller function. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X.of_le)
theorem of_le (hg : Within8P g) (h : ∀ p t, Hyp30 p t → f p t ≤ g p t) : Within8P f :=
  let ⟨C, hC, hg⟩ := hg
  ⟨C, hC, fun p t hp => le_trans (by exact_mod_cast h p t hp) (hg p t hp)⟩

/-- A sum. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X.add)
theorem add (hf : Within8P f) (hg : Within8P g) : Within8P fun p t => f p t + g p t := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, fun p t hp => ?_⟩
  rw [Nat.cast_add, add_mul]
  exact add_le_add (hf p t hp) (hg p t hp)

/-- A multiple. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X.const_mul)
theorem const_mul (c : ℕ) (hf : Within8P f) : Within8P fun p t => c * f p t := by
  obtain ⟨A, hA, hf⟩ := hf
  refine ⟨c * A, by positivity, fun p t hp => ?_⟩
  rw [Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf p t hp) (Nat.cast_nonneg c)

end Within8P

/-- The number 1 is within `cost8P`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (within8X_one)
theorem within8P_one : Within8P fun _ _ => 1 :=
  ⟨1, zero_le_one, fun p t h => by
    simpa using one_le_cost8P h⟩

/-! ### The small summands of the shared stage -/

/-- `N ≥ 1` under the hypotheses of Theorem 30, because `N ≥ √K N₀ ≥ 1`. -/
theorem hyp30_N_pos {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : 1 ≤ p.N := by
  have := (one_le_sqrtKN0 h.m_le).trans h.N_ge
  exact_mod_cast this

/-- The tables, the list of subsets, the directory and the digit tables of the shared stage: at
most `52 N L N₀`, in natural numbers. -/
theorem tables_le {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
        + (p.D + 1) * (p.m + 1)
      ≤ 52 * (p.N * p.L * N0 p.L p.m) := by
  have hL := h.L_pos
  have hLg := h.L_ge
  have hm := h.m_pos
  have hN := hyp30_N_pos h
  have hKn := K_le_N0 h.L_ge
  have hsqrt := Nat.sqrt_le_self p.K
  have hKK : p.KK ≤ p.K := Nat.sqrt_le _
  have hDn := D_le_N0 h.L_ge
  have hLn := L_le_ten_mul_N0 h.L_ge
  have hLo : p.Lo ≤ p.L := Nat.sub_le _ _
  have hn := N0_pos p.L p.m
  let L := p.L
  let N := p.N
  let n := N0 L p.m
  change _ ≤ 52 * (N * L * n)
  change p.K ≤ n at hKn
  change p.D ≤ n at hDn
  change L ≤ 10 * n at hLn
  change 1 ≤ n at hn
  have h1 : L * L ≤ 10 * (N * L * n) := by
    calc L * L ≤ L * (10 * n) := by gcongr
      _ = 10 * (1 * L * n) := by ring
      _ ≤ _ := by gcongr
  have h2 : n ≤ N * L * n := by simpa using
    (Nat.mul_le_mul_right n (Nat.mul_pos hN hL) : 1 * n ≤ N * L * n)
  have h3 : L * n ≤ N * L * n := by simpa using Nat.mul_le_mul_right n (Nat.le_mul_of_pos_left L hN)
  have h4 : N * L ≤ N * L * n := Nat.le_mul_of_pos_right _ hn
  calc _ ≤ (2 * L) ^ 2 + 2 * n + (2 * n) * (2 * L) + (2 * N) * (2 * L) + (2 * n) * L := by
        gcongr <;> omega
    _ = 4 * (L * L) + 2 * n + 6 * (L * n) + 4 * (N * L) := by ring
    _ ≤ _ := by omega

/-- The input array of a band: `bandArrayShape ≤ 5 L 7^L`, because `K₀² N₀ D ≤ K N₀ D ≤ 7^L`. -/
theorem bandArrayShape_le {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    Sec2.bandArrayShape p ≤ 5 * (p.L * 7 ^ p.L) := by
  have hL1 := h.L_pos
  have hKK : p.KK ≤ p.K := Nat.sqrt_le _
  have hKND : p.K * p.N0 * p.D ≤ 7 ^ p.L := Theorem30.K_mul_N0_mul_D_le p.L p.m
  have hentries : p.KK * p.N0 * p.D ≤ 7 ^ p.L :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hKK)) hKND
  have hS1 : 1 ≤ 7 ^ p.L := Nat.one_le_pow _ _ (by norm_num)
  unfold Sec2.bandArrayShape
  change 7 ^ p.L + (p.KK * p.N0 * p.D + 1) * (p.L + 1) ≤ _
  generalize p.KK * p.N0 * p.D = E at *
  generalize 7 ^ p.L = S7 at *
  generalize p.L = L at *
  have harray : (E + 1) * (L + 1) ≤ L * S7 + S7 + L + 1 :=
    (Nat.mul_le_mul_right _ (by omega) : _ ≤ (S7 + 1) * (L + 1)).trans (le_of_eq (by ring))
  have hSL : S7 ≤ L * S7 := Nat.le_mul_of_pos_left _ hL1
  have hLS : L ≤ L * S7 := Nat.le_mul_of_pos_right _ hS1
  omega

/-- The work for one band, `encWorkP + bandArrayShape`, is at most `10 L M/(1 - ρ)`. -/
theorem band_work_le {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    ((encWorkP p.L p.m + Sec2.bandArrayShape p : ℕ) : ℝ)
      ≤ 10 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))) := by
  have hden := sub_pos.2 (sec4_rho_lt_one p.L p.m h.L_ge)
  have hM := le_div_one_sub_rho h.L_ge (Nat.cast_nonneg (M p.L p.m))
  have hL : (1 : ℝ) ≤ p.L := Nat.one_le_cast.2 h.L_pos
  have hseven : (7 : ℝ) ^ p.L ≤ (M p.L p.m : ℝ) := by exact_mod_cast seven_pow_le_M h.L_ge
  have hband : (Sec2.bandArrayShape p : ℝ) ≤ 5 * ((p.L : ℝ) * (7 : ℝ) ^ p.L) := by
    exact_mod_cast bandArrayShape_le h
  have henc := encWorkP_le_M_div h.L_ge
  rw [mul_div_assoc] at henc
  push_cast
  let A := (M p.L p.m : ℝ) / (1 - rho p.L p.m)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpow := hseven.trans hM
  calc _ ≤ 9 / 2 * A + 5 * ((p.L : ℝ) * A) := add_le_add henc (hband.trans (by gcongr))
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.2 hL) hA]

/-- The number of bands times their work is at most twice the encoding summand. -/
theorem within8P_bands :
    Within8P fun p _ => p.nB * (encWorkP p.L p.m + Sec2.bandArrayShape p) := by
  refine ⟨2, by norm_num, fun p t h => ?_⟩
  have hs := sqrtKN0_pos h.m_le
  have hden := sub_pos.2 (sec4_rho_lt_one p.L p.m h.L_ge)
  have hnB : (p.nB : ℝ) ≤ 2 * (p.N : ℝ) / sqrtKN0 p.L p.m := by
    have hb := Theorem30.bands h.m_pos h.L_ge h.N_ge
    change 2 * (p.nB : ℝ) ≤ _ at hb
    linarith only [hb, show 4 * (p.N : ℝ) / sqrtKN0 p.L p.m = 2 * (2 * p.N / sqrtKN0 p.L p.m) by ring]
  let A := (p.N : ℝ) * ((p.L : ℝ) * sqrtKN0 p.L p.m) / (1 - rho p.L p.m)
  rw [Nat.cast_mul]
  calc _ ≤ (2 * (p.N : ℝ) / sqrtKN0 p.L p.m) *
          (10 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m)))) :=
        mul_le_mul hnB (band_work_le h) (Nat.cast_nonneg _) (by positivity)
    _ = 20 * A := by
        dsimp [A]
        rw [← sqrtKN0_sq]
        field_simp
        <;> ring
    _ ≤ 2 * cost8P p.L p.m t p.N := by
        have hA : 0 ≤ A := by dsimp [A]; positivity
        unfold cost8P
        simp only [mul_div_assoc (27 / 2 : ℝ)]
        change 20 * A ≤ 2 * (_ + (27 / 2 : ℝ) * A)
        linarith [cost8X_first_term_nonneg p.L p.m t p.N]

/-- The tables of the shared stage are within `cost8P`: `52 N L N₀ ≤ 52 N L √K N₀`. -/
theorem within8P_tables :
    Within8P fun p _ => (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1)
      + (p.N + 1) * (p.Lo + 1) + (p.D + 1) * (p.m + 1) := by
  refine ⟨26, by norm_num, fun p t h => ?_⟩
  have hN0 := N0_le_sqrtKN0 h.m_le
  have hbase := base_le_cost8P h.L_ge t p.N
  refine (Nat.cast_le.2 (tables_le h)).trans ?_
  push_cast
  calc 52 * ((p.N : ℝ) * p.L * (N0 p.L p.m : ℝ))
      = 52 * ((p.N : ℝ) * ((p.L : ℝ) * (N0 p.L p.m : ℝ))) := by ring
    _ ≤ 52 * ((p.N : ℝ) * ((p.L : ℝ) * sqrtKN0 p.L p.m)) := by gcongr
    _ ≤ _ := by linarith

/-- **The pruned shared stage** runs within `cost8P`. -/
theorem within8P_sharedShapeP : Within8P fun p _ => Sec2.sharedShapeP p :=
  (within8P_tables.add within8P_bands).of_le fun p _ _ => by
    unfold Sec2.sharedShapeP
    exact le_rfl

/-! ### The tiles -/

/-- The work for the boxes: `L` for each box of each tile; `boxes_costX` against the first
summand. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (within8X_boxes)
theorem within8P_boxes : Within8P fun p t => p.L * (p.nB ^ 2 * (boxes p.L p.m t).card) := by
  refine ⟨8, by norm_num, fun p t h => ?_⟩
  have hboxes := boxes_costX h.m_pos h.L_ge h.t_le h.N_ge
  have hden := sub_pos.2 (sec4_rho_lt_one p.L p.m h.L_ge)
  have hs := (one_le_sqrtKN0 h.m_le).trans' zero_le_one
  push_cast
  change (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * _) ≤ _
  unfold cost8P
  have : 0 ≤ 27 / 2 * ((p.N : ℝ) * ((p.L : ℝ) * sqrtKN0 p.L p.m)) / (1 - rho p.L p.m) := by positivity
  linarith

/-- **The tries of all tiles** are built within `cost8P`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (within8X_tAllTiles)
theorem within8P_tAllTiles : Within8P fun p t => tAllTiles p.L p.m t p.nB := by
  obtain ⟨c, hc⟩ := exists_tTile_le
  refine ((within8P_boxes.const_mul c).add (within8P_one.const_mul 30)).of_le fun p t h => ?_
  have htile := hc p.L p.m t h.L_pos h.m_le
  have hn : p.nB ≤ p.nB ^ 2 := Nat.le_self_pow (by norm_num) _
  calc tAllTiles p.L p.m t p.nB
      = p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB * 40 + 30 := by simp only [tAllTiles]; ring
    _ ≤ p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB ^ 2 * 40 + 30 := by gcongr
    _ = p.nB ^ 2 * (tTile p.L p.m t + 120) + 30 := by ring
    _ ≤ p.nB ^ 2 * (c * (p.L * (boxes p.L p.m t).card)) + 30 := by gcongr
    _ = c * (p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) + 30 * 1 := by ring

/-! ### The two quantities of the set-up -/

/-- `N (L + 1)` is within `cost8P`: `N (L + 1) ≤ 2 N L ≤ 2 N L √K N₀`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (N_mul_le_cost8X)
theorem N_mul_le_cost8P {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * ((p.L : ℝ) + 1) ≤ cost8P p.L p.m t p.N := by
  have hs := one_le_sqrtKN0 h.m_le
  have hL : (1 : ℝ) ≤ p.L := Nat.one_le_cast.2 h.L_pos
  calc _ ≤ (p.N : ℝ) * (2 * (p.L : ℝ)) := by gcongr; linarith
    _ = 2 * ((p.N : ℝ) * ((p.L : ℝ) * 1)) := by ring
    _ ≤ 2 * ((p.N : ℝ) * ((p.L : ℝ) * sqrtKN0 p.L p.m)) := by gcongr
    _ ≤ _ := base_le_cost8P h.L_ge t p.N

/-- `N 4^m` is within `cost8P`: `4^m = D ≤ N₀ ≤ √K N₀ ≤ L √K N₀`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (N_mul_pow_le_cost8X)
theorem N_mul_pow_le_cost8P {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ cost8P p.L p.m t p.N := by
  have hD : (4 : ℝ) ^ p.m ≤ (N0 p.L p.m : ℝ) := by exact_mod_cast D_le_N0 h.L_ge
  have hL : (1 : ℝ) ≤ p.L := Nat.one_le_cast.2 h.L_pos
  have hs := one_le_sqrtKN0 h.m_le
  calc _ ≤ (p.N : ℝ) * (1 * sqrtKN0 p.L p.m) := by
        rw [one_mul]
        gcongr
        exact hD.trans (N0_le_sqrtKN0 h.m_le)
    _ ≤ 2 * ((p.N : ℝ) * ((p.L : ℝ) * sqrtKN0 p.L p.m)) := by
        rw [← one_mul ((p.N : ℝ) * (1 * sqrtKN0 p.L p.m))]
        gcongr <;> norm_num
    _ ≤ _ := base_le_cost8P h.L_ge t p.N

/-- **The pruned preprocessing** takes `O(cost8P)` steps. `c` is the constant of the pruned shared
stage. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (exists_tPreCore_leX)
theorem exists_tPreCore_leP (c : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tPreCoreP c p t : ℝ) ≤ C * cost8P p.L p.m t p.N :=
  (((within8P_sharedShapeP.const_mul c).add within8P_tAllTiles).add
    (within8P_one.const_mul 300)).of_le fun _ _ _ => le_of_eq (by simp [tPreCoreP])

end ImprovedExponents
