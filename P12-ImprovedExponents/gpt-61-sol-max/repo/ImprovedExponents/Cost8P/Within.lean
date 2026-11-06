module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
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
theorem pow_le_pow_sub_of_ten_mul_le {a b L m} (hb : 0 < b) (hab : a ^ 10 ≤ b ^ 9)
    (hL : 10 * m ≤ L) : a ^ L ≤ b ^ (L - m) := by
  rw [← Nat.pow_le_pow_iff_left (by norm_num : 10 ≠ 0)]
  calc (a ^ L) ^ 10 = (a ^ 10) ^ L := by ring
    _ ≤ (b ^ 9) ^ L := Nat.pow_le_pow_left hab L
    _ = b ^ (9 * L) := by rw [← pow_mul]
    _ ≤ b ^ (10 * (L - m)) := Nat.pow_le_pow_right hb (by omega)
    _ = (b ^ (L - m)) ^ 10 := by rw [← pow_mul, mul_comm]

/-- `K = binom(L, m) ≤ 2^L ≤ 3^{L-m} = N₀` for `10 m ≤ L`. -/
theorem K_le_N0 {L m} (hL : 10 * m ≤ L) : K L m ≤ N0 L m :=
  (Nat.choose_le_two_pow L m).trans (pow_le_pow_sub_of_ten_mul_le (by norm_num) (by norm_num) hL)

/-- `D = 4^m ≤ 3^{9m} ≤ 3^{L-m} = N₀` for `10 m ≤ L`. -/
def D_le_N0 {L m} (hL : 10 * m ≤ L) :=
  calc D m = 4 ^ m := rfl
    _ ≤ (3 ^ 9) ^ m := Nat.pow_le_pow_left (by norm_num) m
    _ = 3 ^ (9 * m) := by rw [← pow_mul]
    _ ≤ 3 ^ (L - m) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `L ≤ 10 (L - m) ≤ 10 N₀` for `10 m ≤ L`. -/
def L_le_ten_mul_N0 {L m} (hL : 10 * m ≤ L) :=
  calc L ≤ 10 * (L - m) := by omega
    _ ≤ 10 * 3 ^ (L - m) := Nat.mul_le_mul_left _ (Nat.lt_pow_self (by norm_num)).le

/-- `7^L ≤ 9^{L-m} = N₀² ≤ K N₀² = M` for `10 m ≤ L`. -/
def seven_pow_le_M {L m} hL :=
  calc 7 ^ L ≤ 9 ^ (L - m) := pow_le_pow_sub_of_ten_mul_le (by norm_num) (by norm_num) hL
    _ = N0 L m ^ 2 := by
        change (3 ^ 2) ^ (L - m) = (3 ^ (L - m)) ^ 2
        rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ K L m * N0 L m ^ 2 := Nat.le_mul_of_pos_left _ (Nat.choose_pos (by omega))

/-! ### The second summand of `cost8P` -/

/-- `√K N₀ ≥ N₀ ≥ 1`. -/
theorem one_le_sqrtKN0 {L m} (hmL : m ≤ L) : 1 ≤ sqrtKN0 L m := by
  have hK : (1 : ℝ) ≤ Real.sqrt (K L m) :=
    Real.one_le_sqrt.2 (mod_cast Nat.choose_pos hmL)

  exact one_le_mul_of_one_le_of_one_le hK (mod_cast N0_pos L m)

/-- `N₀ ≤ √K N₀`. -/
theorem N0_le_sqrtKN0 {L m} (hmL : m ≤ L) : (N0 L m : ℝ) ≤ sqrtKN0 L m := by
  have hK : (1 : ℝ) ≤ Real.sqrt (K L m) :=
    Real.one_le_sqrt.2 (mod_cast Nat.choose_pos hmL)
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) hK

variable {L m : ℕ} (hL : 10 * m ≤ L)

include L m hL in
/-- The second summand of `cost8P` is not negative. -/
theorem cost8P_second_term_nonneg  (N : ℕ) :
    0 ≤ (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m := by
  have  := sec4_rho_lt_one L m hL
  have  := sqrtKN0_pos (L := L) (m := m) (by omega)
  positivity

include L m hL in
/-- **The base `N L √K N₀`**: the second summand of `cost8P` is at least `(27/2) N L √K N₀`,
because `M/√K N₀ = √K N₀` and `1/(1 - ρ) ≥ 1`. -/
theorem base_le_cost8P  (t N : ℕ) :
    27 / 2 * ((N : ℝ) * (L : ℝ) * sqrtKN0 L m) ≤ cost8P L m t N := by
  have  := cost8X_first_term_nonneg L m t N
  have  := rho_nonneg hL

  have  := (sqrtKN0_pos (L := L) (m := m) (by omega)).le
  have  : 0 ≤ (N : ℝ) * (L : ℝ) * sqrtKN0 L m := by positivity
  have  : 27 / 2 * (N : ℝ) * (L : ℝ) * sqrtKN0 L m
      ≤ (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m := by
    rw [encodingP_eq (by omega), le_div_iff₀ (sub_pos.2 (sec4_rho_lt_one L m hL))]
    nlinarith
  unfold cost8P
  linarith

/-- `cost8P` is at least 1 (for `L ≥ 1`; at `L = 0` it vanishes). -/
theorem one_le_cost8P (L m t N : ℕ) (hL1 : 1 ≤ L) (hL : 10 * m ≤ L)
    (hN : sqrtKN0 L m ≤ (N : ℝ)) : 1 ≤ cost8P L m t N := by
  have  := base_le_cost8P hL t N
  have hs1 := one_le_sqrtKN0 (L := L) (m := m) (by omega)

  have hL1 : (1 : ℝ) ≤ L := mod_cast hL1
  have :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hs1.trans hN) hL1) hs1
  linarith

/-! ### `Within8P` -/

/-- `f = O(cost8P)`: at most a constant times `cost8P`, for all parameters that satisfy the
hypotheses of Theorem 30. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X)
def Within8P (f : Sec2.Par → ℕ → ℕ) :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, Hyp30 p t → f p t ≤ C * cost8P p.L p.m t p.N

namespace Within8P

variable {f g : Sec2.Par → ℕ → ℕ}

/-- A smaller function. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X.of_le)
theorem of_le (hg : Within8P g) (h : ∀ p t, Hyp30 p t → f p t ≤ g p t) : Within8P f :=
  let ⟨C, hC, hg⟩ := hg
  ⟨C, hC, fun p t hp => le_trans (mod_cast h p t hp) (hg p t hp)⟩

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
theorem const_mul c (hf : Within8P f) : Within8P fun p t => c * f p t := by
  obtain ⟨A, hA, hf⟩ := hf
  refine ⟨c * A, by positivity, fun p t hp => ?_⟩
  grind [mul_assoc, mul_le_mul_of_nonneg_left]

end Within8P

/-- The number 1 is within `cost8P`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (within8X_one)
theorem within8P_one : Within8P fun _ _ => 1 :=
  ⟨1, zero_le_one, fun p t h => by
    simpa using one_le_cost8P p.L p.m t p.N h.L_pos h.L_ge h.N_ge⟩

/-! ### The small summands of the shared stage -/

/-- `N ≥ 1` under the hypotheses of Theorem 30, because `N ≥ √K N₀ ≥ 1`. -/
theorem hyp30_N_pos {p} {t} (h : Hyp30 p t) : 1 ≤ p.N := by
  have := (one_le_sqrtKN0 h.m_le).trans h.N_ge
  exact_mod_cast this

/-- The tables, the list of subsets, the directory and the digit tables of the shared stage: at
most `52 N L N₀`, in natural numbers. -/
theorem tables_le {p} {t} (h : Hyp30 p t) :
    (p.L + 1) ^ 2 + Nat.sqrt p.K + 1 + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
        + (p.D + 1) * (p.m + 1)
      ≤ 52 * (p.N * p.L * N0 p.L p.m) := by
  have hL := h.L_ge
  have  := h.m_pos
  have  := hyp30_N_pos h
  have  : p.K ≤ N0 p.L p.m := K_le_N0 hL
  have  : Nat.sqrt p.K ≤ p.K := Nat.sqrt_le_self _
  have  : p.KK ≤ p.K := Nat.sqrt_le _
  have  : p.D ≤ N0 p.L p.m := D_le_N0 hL
  have  : p.L ≤ 10 * N0 p.L p.m := L_le_ten_mul_N0 hL
  have  : p.Lo ≤ p.L := Nat.sub_le _ _
  have  : 1 ≤ N0 p.L p.m := N0_pos p.L p.m
  generalize N0 p.L p.m = n at *
  generalize p.K = K at *
  generalize p.KK = KK at *
  generalize p.D = D at *
  generalize p.Lo = Lo at *
  generalize p.N = N at *
  generalize p.L = L at *
  generalize p.m = m at *
  have  :=
    calc (L + 1) ^ 2 ≤ (2 * L) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (L * L) := by ring
      _ ≤ 4 * (L * (10 * n)) := by gcongr
      _ = 40 * (1 * L * n) := by ring
      _ ≤ 40 * (N * L * n) := by gcongr
  have  :=
    calc Nat.sqrt K + 1 ≤ 2 * n := by omega
      _ = 2 * (1 * 1 * n) := by ring
      _ ≤ 2 * (N * L * n) := by gcongr; omega
  have  :=
    calc (KK + 1) * (L + 1) ≤ 2 * n * (2 * L) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 * (1 * L * n) := by ring
      _ ≤ 4 * (N * L * n) := by gcongr
  have  :=
    calc (N + 1) * (Lo + 1) ≤ 2 * N * (2 * L) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 * (N * L * 1) := by ring
      _ ≤ 4 * (N * L * n) := by gcongr
  have  :=
    calc (D + 1) * (m + 1) ≤ 2 * n * L := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (1 * L * n) := by ring
      _ ≤ 2 * (N * L * n) := by gcongr
  generalize N * L * n = P at *
  omega

/-- The input array of a band: `bandArrayShape ≤ 5 L 7^L`, because `K₀² N₀ D ≤ K N₀ D ≤ 7^L`. -/
theorem bandArrayShape_le {p} {t} (h : Hyp30 p t) :
    Sec2.bandArrayShape p ≤ 5 * (p.L * 7 ^ p.L) := by
  have  := h.L_pos


  have  : p.KK * p.N0 * p.D ≤ 7 ^ p.L :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sqrt_le _))) (Theorem30.K_mul_N0_mul_D_le p.L p.m)
  have  : 1 ≤ 7 ^ p.L := Nat.one_le_pow _ _ (by norm_num)
  unfold Sec2.bandArrayShape
  change 7 ^ p.L + (p.KK * p.N0 * p.D + 1) * (p.L + 1) ≤ _
  generalize p.KK * p.N0 * p.D = E at *
  nlinarith

/-- The work for one band, `encWorkP + bandArrayShape`, is at most `10 L M/(1 - ρ)`. -/
theorem band_work_le {p} {t} (h : Hyp30 p t) :
    ((encWorkP p.L p.m + Sec2.bandArrayShape p : ℕ) : ℝ)
      ≤ 10 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))) := by
  have hL := h.L_ge

  have  := rho_nonneg hL
  have hM0 : (0 : ℝ) ≤ (M p.L p.m : ℝ) := Nat.cast_nonneg _
  have hMρ :=
    le_div_self hM0 (sub_pos.2 (sec4_rho_lt_one p.L p.m hL)) (by linarith)


  have  := by
    have := encWorkP_le_M_div hL
    rwa [mul_div_assoc] at this
  have  : ((7 : ℕ) : ℝ) ^ p.L ≤ (M p.L p.m : ℝ) := mod_cast seven_pow_le_M hL
  have  : (Sec2.bandArrayShape p : ℝ) ≤ 5 * ((p.L : ℝ) * (7 : ℝ) ^ p.L) := mod_cast bandArrayShape_le h
  have  : 5 * (p.L : ℝ) * (7 : ℝ) ^ p.L
      ≤ 5 * (p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m)) := by
    ram_safe
  have  : 9 / 2 * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))
      ≤ 9 / 2 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hM0.trans hMρ) (mod_cast h.L_pos)) (by norm_num)
  push_cast
  linarith

/-- The work for the bands: `nB (encWorkP + bandArrayShape)` is at most twice the second summand of
`cost8P`, because `nB ≤ 2 N/(√K N₀)`. -/
theorem within8P_bands :
    Within8P fun p _ => p.nB * (encWorkP p.L p.m + Sec2.bandArrayShape p) := by
  refine ⟨2, by norm_num, fun p t h => ?_⟩
  have hL := h.L_ge
  have  := sqrtKN0_pos h.m_le
  have  := sec4_rho_lt_one p.L p.m hL
  have hnB : (p.nB : ℝ) ≤ 2 * (p.N : ℝ) / sqrtKN0 p.L p.m := by
    have := Theorem30.bands h.m_pos hL h.N_ge
    change (2 * numBands p.L p.m p.N : ℝ) ≤ _ at this
    have h2 : (p.nB : ℝ) = (numBands p.L p.m p.N : ℝ) := rfl
    have  : 4 * (p.N : ℝ) / sqrtKN0 p.L p.m = 2 * (2 * (p.N : ℝ) / sqrtKN0 p.L p.m) := by
      ring
    rw [h2]
    linarith

  have  := cost8X_first_term_nonneg p.L p.m t p.N
  have  : 0 ≤ (p.N : ℝ) * (p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m)) / sqrtKN0 p.L p.m :=
    by positivity
  have  :=
    mul_le_mul hnB (band_work_le h) (Nat.cast_nonneg _) (by positivity)
  have  : 2 * (p.N : ℝ) / sqrtKN0 p.L p.m
        * 10 * (p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))
      = 20 * ((p.N : ℝ) * (p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))
          / sqrtKN0 p.L p.m) := by ring
  have heq' : 2 * ((p.N : ℝ) * (p.L : ℝ) * (27 / 2 * (M p.L p.m : ℝ) / (1 - rho p.L p.m))
        / sqrtKN0 p.L p.m)
      = 27 * ((p.N : ℝ) * (p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))
          / sqrtKN0 p.L p.m) := by ring
  rw [Nat.cast_mul]
  unfold cost8P
  rw [mul_add, heq']
  linarith

/-- The tables of the shared stage are within `cost8P`: `52 N L N₀ ≤ 52 N L √K N₀`. -/
theorem within8P_tables :
    Within8P fun p _ => (p.L + 1) ^ 2 + Nat.sqrt p.K + 1 + (p.KK + 1) * (p.L + 1)
      + (p.N + 1) * (p.Lo + 1) + (p.D + 1) * (p.m + 1) := by
  refine ⟨52 * 2 / 27, by norm_num, fun p t h => ?_⟩

  have  := base_le_cost8P h.L_ge t p.N
  have  := N0_le_sqrtKN0 h.m_le
  have  : (((p.L + 1) ^ 2 + Nat.sqrt p.K + 1 + (p.KK + 1) * (p.L + 1)
        + (p.N + 1) * (p.Lo + 1) + (p.D + 1) * (p.m + 1) : ℕ) : ℝ)
      ≤ 52 * ((p.N : ℝ) * (p.L : ℝ) * (N0 p.L p.m : ℝ)) := mod_cast tables_le h
  have  : 52 * ((p.N : ℝ) * (p.L : ℝ) * (N0 p.L p.m : ℝ))
      ≤ 52 * ((p.N : ℝ) * (p.L : ℝ) * sqrtKN0 p.L p.m) := by gcongr
  linarith

/-- **The pruned shared stage** runs within `cost8P`. -/
theorem within8P_sharedShapeP : Within8P fun p _ => Sec2.sharedShapeP p :=
  (within8P_tables.add within8P_bands).of_le fun p _ _ => by
    rfl

/-! ### The tiles -/

/-- The work for the boxes: `L` for each box of each tile; `boxes_costX` against the first
summand. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (within8X_boxes)
theorem within8P_boxes : Within8P fun p t => p.L * (p.nB ^ 2 * (boxes p.L p.m t).card) := by
  refine ⟨8, by norm_num, fun p t h => ?_⟩
  have  := boxes_costX h.m_pos h.L_ge h.t_le h.N_ge
  have  := cost8P_second_term_nonneg h.L_ge p.N
  push_cast
  change (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * _) ≤ _
  unfold cost8P
  linarith

/-- **The tries of all tiles** are built within `cost8P`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (within8X_tAllTiles)
theorem within8P_tAllTiles : Within8P fun p t => tAllTiles p.L p.m t p.nB := by
  obtain ⟨c, hc⟩ := exists_tTile_le
  refine ((within8P_boxes.const_mul c).add (within8P_one.const_mul 30)).of_le fun p t h => ?_
  have  := hc p.L p.m t h.L_pos h.m_le
  have  : p.nB ≤ p.nB ^ 2 := Nat.le_self_pow (by norm_num) _
  calc tAllTiles p.L p.m t p.nB
      = p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB * 40 + 30 := by simp only [tAllTiles]; ring
    _ ≤ p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB ^ 2 * 40 + 30 := by gcongr
    _ = p.nB ^ 2 * (tTile p.L p.m t + 120) + 30 := by ring
    _ ≤ p.nB ^ 2 * (c * (p.L * (boxes p.L p.m t).card)) + 30 := by gcongr
    _ = c * (p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) + 30 * 1 := by ring

/-! ### The two quantities of the set-up -/

/-- `N (L + 1)` is within `cost8P`: `N (L + 1) ≤ 2 N L ≤ 2 N L √K N₀`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (N_mul_le_cost8X)
theorem N_mul_le_cost8P {p} {t} (h : Hyp30 p t) :
    (p.N : ℝ) * ((p.L : ℝ) + 1) ≤ cost8P p.L p.m t p.N := by
  have  := base_le_cost8P h.L_ge t p.N
  have  := one_le_sqrtKN0 h.m_le
  have  : (1 : ℝ) ≤ (p.L : ℝ) := mod_cast h.L_pos
  have  : 0 ≤ (p.N : ℝ) * (p.L : ℝ) := by positivity
  nlinarith

/-- `N 4^m` is within `cost8P`: `4^m = D ≤ N₀ ≤ √K N₀ ≤ L √K N₀`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (N_mul_pow_le_cost8X)
theorem N_mul_pow_le_cost8P {p} {t} (h : Hyp30 p t) :
    (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ cost8P p.L p.m t p.N := by
  have  := base_le_cost8P h.L_ge t p.N
  have  : ((4 : ℕ) : ℝ) ^ p.m ≤ (N0 p.L p.m : ℝ) := mod_cast D_le_N0 h.L_ge
  have  := N0_le_sqrtKN0 h.m_le
  have  := mod_cast h.L_pos
  have  := (sqrtKN0_pos h.m_le).le
  have  : (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ (p.N : ℝ) * sqrtKN0 p.L p.m := by
    ram_arith
  have  : (p.N : ℝ) * sqrtKN0 p.L p.m ≤ (p.N : ℝ) * (p.L : ℝ) * sqrtKN0 p.L p.m := by
    bound
  have  : 0 ≤ (p.N : ℝ) * (p.L : ℝ) * sqrtKN0 p.L p.m := by positivity
  linarith

/-- **The pruned preprocessing** takes `O(cost8P)` steps. `c` is the constant of the pruned shared
stage. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (exists_tPreCore_leX)
theorem exists_tPreCore_leP c : ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, Hyp30 p t →
    tPreCoreP c p t ≤ C * cost8P p.L p.m t p.N :=
  (((within8P_sharedShapeP.const_mul c).add within8P_tAllTiles).add
    (within8P_one.const_mul 300)).of_le fun _ _ _ => le_of_eq rfl

end ImprovedExponents
