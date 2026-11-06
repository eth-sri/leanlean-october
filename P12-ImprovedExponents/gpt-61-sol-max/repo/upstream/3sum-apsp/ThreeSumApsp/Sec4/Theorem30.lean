/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Sec2.Tiling
public import ThreeSumApsp.Sec4.Lemma27_28
public import ThreeSumApsp.Sec4.Lemma29
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Equation (7) and Theorem 30: the data structure (Section 4.3)

The running times of Theorem 30 on the word RAM are `wordRam_theorem_30` and
`wordRam_theorem_30_wanted`; the expressions inside their `O(·)` are `cost8`, `cost9` and
`costQuery`. This file has the mathematics of the paper's proof, in the paper's order.

* *The decay rate.* `ρ = 9m/(L-m+1)` is less than 1 (`sec4_rho_lt_one`), the ratio `β_d/β_{d-1}` is
  at most `ρ` (`eq_7_ratio`), and so `β_d ≤ ρ^d M` (`eq_7`). This is equation (7).
* *Preprocessing: the count behind (8).* Here `sqrtKN0 L m` is `√K N₀`. Padding at most doubles `N`
  (`Theorem30.padding`; nothing else rests on this lemma). The list of subsets takes `K L ≤ 10^L`
  operations (`Theorem30.subsets`), which the last term of (8) absorbs
  (`Theorem30.subsets_absorbed`). There are at most `4N/(√K N₀)` bands (`Theorem30.bands`), with `N`
  the given size, by a slightly finer count than `K₀ ≥ √K/2` gives (`Theorem30.numBands_mul_le`);
  the input array of a band has at most `K N₀ D ≤ 7^L` nonzero entries
  (`Theorem30.K_mul_N0_mul_D_le`), and `L · 7^L ≤ 2 · 10^L` (`Theorem30.form_array`). There are at
  most `4N²/M` tiles (`Theorem30.tiles`) with at most `(m+1) ∑_{d ≥ t} β_d` boxes each (Lemma 29),
  and `∑_{d ≥ t} β_d ≤ M ρ^t/(1-ρ)` by (7) (`Theorem30.sum_beta`), which bounds the number of all
  boxes (`Theorem30.boxes_total`). The boxes (`Theorem30.boxes_cost`), the bands
  (`Theorem30.bands_cost`) and the list add up to at most a constant times the expression in (8)
  (`Theorem30.cost8_assembly`).
* *Query.* The sum of Lemma 28 for the output string of the position `(I, J)` is `(XY)[I, J]` by
  Section 2.4.4 (`Theorem30.query`). Each box of that sum is a box of the tile (`Theorem30.lookup`),
  and the dynamic program of Lemma 29 has stored its value (`dpValue_card_starLevels`); so the query
  returns `(XY)[I, J]` (`Theorem30.correct`). Expression (9) is `|W|` queries on top of (8)
  (`Theorem30.cost9_eq`).
* *Word size.* `10^L ≤ N^{5/2}` (`Theorem30.ten_pow_le`).

Here `N` is the given size throughout, and the padded size is `padN L m N`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### The decay rate `ρ` and equation (7) -/

/-- Section 4.3: `ρ = 9m/(L-m+1)` "is less than 1 since L ≥ 10m". -/
theorem sec4_rho_lt_one L m (hL : 10 * m ≤ L) : rho L m < 1 := by
  have  : (10 : ℝ) * m ≤ L := mod_cast hL
  rw [rho, div_lt_one (by linarith)]
  linarith

/-- The decay rate `ρ` is not negative when `L ≥ 10m`. -/
theorem rho_nonneg {L m} (hL : 10 * m ≤ L) : 0 ≤ rho L m := by
  have  : (10 : ℝ) * m ≤ L := mod_cast hL
  exact div_nonneg (by positivity) (by linarith)

/-! ### Theorem 30, "Preprocessing": the count behind (8) -/

/-- The number `√K N₀` of the hypothesis "N ≥ √K N₀" of Theorem 30 and of the last term of (8). -/
noncomputable def sqrtKN0 L m := Real.sqrt (K L m) * (N0 L m : ℝ)

/-- `√K N₀` is positive when `m ≤ L`. -/
theorem sqrtKN0_pos {L m} (hmL : m ≤ L) : 0 < sqrtKN0 L m := by


  exact mul_pos (Real.sqrt_pos.mpr (mod_cast Nat.choose_pos hmL)) (mod_cast N0_pos L m)

/-- `(√K N₀)² = K N₀² = M`. -/
theorem sqrtKN0_sq L m : sqrtKN0 L m ^ 2 = (M L m : ℝ) := by
  ram_arith [sqrtKN0, mul_pow, M]

/-- Proof of Theorem 30, "Preprocessing": "we store the K₀² subsets, in O(KL) ≤ O(10^L) operations".
Read as the inequality `K L ≤ 10^L` (constant 1). -/
theorem Theorem30.subsets L m : K L m * L ≤ 10 ^ L := by
  calc K L m * L ≤ 2 ^ L * 2 ^ L :=
        Nat.mul_le_mul (Nat.choose_le_two_pow L m) Nat.lt_two_pow_self.le
    _ = 4 ^ L := by rw [← Nat.mul_pow]
    _ ≤ 10 ^ L := Nat.pow_le_pow_left (by norm_num) L

/-- `binom(L, r) ≥ L` for `1 ≤ r ≤ L/2`: up to the middle the binomial coefficients increase. -/
private lemma le_choose_of_le_half (L : ℕ) : ∀ r, 1 ≤ r → r ≤ L / 2 → L ≤ L.choose r := by
  intro r h1
  induction r, h1 using Nat.le_induction with
  | base => intro _; simp
  | succ r hr ih =>
    grind [Nat.choose_le_succ_of_lt_half_left]

/-- `K₀ ≥ 3` in the range of Theorem 30, because `K = binom(L, m) ≥ L ≥ 10`. -/
private lemma three_le_K0 (L m : ℕ) (hm : 1 ≤ m) (hL : 10 * m ≤ L) : 3 ≤ K0 L m := by
  have  : L ≤ K L m := le_choose_of_le_half L m hm (by omega)
  exact Nat.le_sqrt.2 (by omega)

variable {L m N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L)
    (hN : sqrtKN0 L m ≤ N)

include L m N hm hL hN in
/-- The number `b` of row bands, `N/(K₀ N₀)` rounded up, satisfies `b √K N₀ ≤ 2N`. The two bounds of
the paper's proof on the numbers of bands and of tiles rest on this. If `b ≤ 2` it is the hypothesis
`N ≥ √K N₀`. If `b ≥ 3` then `(b - 1) K₀ N₀ < N`, `b ≤ 3(b - 1)/2`, and `√K ≤ K₀ + 1 ≤ 4K₀/3`. -/
theorem Theorem30.numBands_mul_le  :
    (numBands L m N : ℝ) * sqrtKN0 L m ≤ 2 * (N : ℝ) := by
  have hN0  := mod_cast N0_pos L m
  have hK0 : (3 : ℝ) ≤ (K0 L m : ℝ) := mod_cast three_le_K0 L m hm hL
  have hsqrt : Real.sqrt (K L m) ≤ (K0 L m : ℝ) + 1 :=
    Real.sqrt_le_iff.2 ⟨by positivity, mod_cast (Nat.lt_succ_sqrt' (K L m)).le⟩
  have hband : 0 < (K0 L m : ℝ) * (N0 L m : ℝ) := by positivity
  -- `b` is `N/(K₀ N₀)` rounded up
  have hceil : (numBands L m N : ℝ) * ((K0 L m : ℝ) * (N0 L m : ℝ))
      ≤ (N : ℝ) + (K0 L m : ℝ) * (N0 L m : ℝ) := by
    have  : numBands L m N * bandSize L m ≤ N + bandSize L m - 1 := Nat.div_mul_le_self _ _

    exact_mod_cast by
      ram_arith [bandSize]
  rcases Nat.lt_or_ge (numBands L m N) 3 with hb | hb
  · have hb' : (numBands L m N : ℝ) ≤ 2 := by ram_arith
    exact (mul_le_mul_of_nonneg_right hb' (sqrtKN0_pos (by omega)).le).trans
      (mul_le_mul_of_nonneg_left hN zero_le_two)
  · have hb' : (3 : ℝ) ≤ (numBands L m N : ℝ) := mod_cast hb
    have hwide : sqrtKN0 L m ≤ 4 / 3 * (K0 L m : ℝ) * (N0 L m : ℝ) := by
      unfold sqrtKN0
      nlinarith [hsqrt, hK0, hN0]
    -- `b √K N₀ ≤ (4b/3) K₀ N₀ ≤ 2 (b - 1) K₀ N₀ ≤ 2N`
    nlinarith [mul_le_mul_of_nonneg_left hwide (by linarith : (0 : ℝ) ≤ (numBands L m N : ℝ)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (numBands L m N : ℝ) - 3) hband.le, hceil]

include L m N hm hL hN in
/-- Proof of Theorem 30, "Preprocessing": "all row bands and column bands, at most 4N/(√K N₀) of
them". There are `numBands L m N` row bands and as many column bands. Here `N` is the given size,
not the padded one, and the bound comes from `Theorem30.numBands_mul_le`. -/
theorem Theorem30.bands  :
    (2 * numBands L m N : ℝ) ≤ 4 * (N : ℝ) / sqrtKN0 L m := by
  rw [le_div_iff₀ (sqrtKN0_pos (by omega))]
  linarith [Theorem30.numBands_mul_le hm hL hN]

/-- Proof of Theorem 30, "Preprocessing": "K N₀ D ≤ 7^L". This bounds the number of nonzero entries
of the input array of a band, which is why forming it takes `O(L · 7^L)` operations. -/
theorem Theorem30.K_mul_N0_mul_D_le L m : K L m * N0 L m * D m ≤ 7 ^ L := by
  -- one summand of the binomial expansion of `(4 + 3)^L`
  calc K L m * N0 L m * D m = L.choose m * 4 ^ m * 3 ^ (L - m) := by unfold K N0 D; ring
    _ ≤ 7 ^ L := Nat.choose_mul_pow_mul_pow_le 4 3 L m

/-- Proof of Theorem 30, "Preprocessing": forming the input array of a band takes "O(L · 7^L)
operations", which is within the "O(10^L) operations" of its encoding ("This is the last term of
(8)"). Read as the inequality `L · 7^L ≤ 2 · 10^L`; the constant 1 fails at `L = 3`. From `L = 3`
on, one more level multiplies the left-hand side by `7(L+1)/L ≤ 10`. -/
theorem Theorem30.form_array : ∀ L , L * 7 ^ L ≤ 2 * 10 ^ L
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | L + 4 =>
    calc (L + 4) * 7 ^ (L + 4) = 7 * (L + 4) * 7 ^ (L + 3) := by ring
      _ ≤ 10 * (L + 3) * 7 ^ (L + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 * ((L + 3) * 7 ^ (L + 3)) := by ring
      _ ≤ 10 * (2 * 10 ^ (L + 3)) := Nat.mul_le_mul_left _ (Theorem30.form_array (L + 3))
      _ = 2 * 10 ^ (L + 4) := by ring

include L m N hm hL hN in
/-- Proof of Theorem 30, "Preprocessing": "the at most 4N²/M tiles, where M = K N₀² is the number of
output entries of a tile". There are `(numBands L m N)²` tiles. Here `N` is the given size, and the
bound comes from `Theorem30.numBands_mul_le`. -/
theorem Theorem30.tiles  :
    (numBands L m N : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 / (M L m : ℝ) := by
  have hpos := sqrtKN0_pos (L := L) (m := m) (by omega)
  rw [← sqrtKN0_sq, le_div_iff₀ (pow_pos hpos 2)]
  calc (numBands L m N : ℝ) ^ 2 * sqrtKN0 L m ^ 2
      = ((numBands L m N : ℝ) * sqrtKN0 L m) ^ 2 := (mul_pow _ _ 2).symm
    _ ≤ (2 * (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (Theorem30.numBands_mul_le hm hL hN) 2
    _ = 4 * (N : ℝ) ^ 2 := by ring

/-! ### Theorem 30, "Query": a query returns `(XY)[I, J]` -/

/-- Proof of Theorem 30, "Query". "Given (I, J), we find its tile from the bands of row I and column
J, the subset Q of its block product, and its output string w […]. We then compute (X_Q Y_Q)[w] as
the sum in Lemma 28 […]. By Section 2.4.4, the sum is (XY)[I, J]." Here `a` and `b` are the input
arrays of the row band of `I` and of the column band of `J`, and `lay` is any choice of the indexing
bijections and of the subsets of the block products; it carries `m ≤ L`. (The hypotheses `m ≥ 1`,
`L ≥ 10m` and `N ≥ √K N₀` of Theorem 30 are not needed for correctness.) -/
theorem Theorem30.query {L m N} t (ht : t ≤ m) (lay : Layout L m)
     X Y (I J : Fin N) :
    querySum m t (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J))
        (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Lemma28.Mult_eq_querySum m t ht _ _ _ (card_innerSetO_outStrOfPos lay I J)]
  exact Mult_bandArray_eq_mul lay X Y I J

/-- Proof of Theorem 30, "Query": "for every V ⊆ Q with |V| = m - t and every box of 𝓑_V, we look up
its value in the trie of the tile." It is there: it is a box. -/
theorem Theorem30.lookup {L m t} {η} {V} (hV : V ∈ Vsets m t η)
    {π} (hπ : π ∈ BV η V) : π ∈ boxes L m t :=
  mem_boxes.2 (BV_isBox hV hπ)

/-- What the dynamic program of Lemma 29 computes for a box, at the number of stars of the box, is
the value of the box. -/
def dpValue_card_starLevels {L m t} a b {π}
     hπ :=
  lemma_29_values L m t _ a b π
    (mem_boxesWithStars.2 ⟨mem_boxes.1 hπ, rfl⟩)

/-- A query, as in the proof of Theorem 30, for the output string `η` of the queried position,
reading only the two encodings of the tile and the stored values of its boxes: "for each such leaf τ
we look up its two numbers Φ_τ(a) and Ψ_τ(b) in the encodings of the tile and multiply them. The
second part is the sum of the values of the boxes of w: for every V ⊆ Q with |V| = m - t and every
box of 𝓑_V, we look up its value in the trie of the tile." The value stored for a box `π` with `e`
stars is the one that the dynamic program computed, `dpValue encA encB e π`. -/
def queryValue {L} m t encA encB (η : OutStr L) :=
  ∑ τ ∈ lowLeaves m t η, encA τ * encB τ
    + ∑ V ∈ Vsets m t η, ∑ π ∈ BV η V, dpValue encA encB (Cube.starLevels π).card π

/-- **Theorem 30**, correctness of the data structure from end to end: the preprocessing computes
the encodings of the bands and, from them, the values of the boxes of every tile by the dynamic
program of Lemma 29; a query for `(I, J)` reads only the two encodings of its tile and the stored
values of boxes, and returns `(XY)[I, J]`. -/
theorem Theorem30.correct {L m N} t (ht : t ≤ m) (lay : Layout L m)
     X Y (I J : Fin N) :
    queryValue m t (encodingL (bandArrayL lay X (bandOf L m I)))
        (encodingR (bandArrayR lay Y (bandOf L m J))) (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Theorem30.query t ht lay X Y I J]
  unfold queryValue querySum
  -- the products at the leaves are read from the encodings, by definition; the stored values of the
  -- boxes are their values, by Lemma 29
  congr 1
  exact sum_congr rfl fun V hV => sum_congr rfl fun π hπ =>
    dpValue_card_starLevels _ _ (Theorem30.lookup hV hπ)

/-! ### Theorem 30, "Word size" -/

/-- Proof of Theorem 30, "Word size": "Since N ≥ N₀ = 3^{L-m} and L ≥ 10m, we have 10^L ≤ N^{5/2}".
Stated after squaring, to stay in the natural numbers. -/
theorem Theorem30.ten_pow_le L m N (hL : 10 * m ≤ L) (hN : N0 L m ≤ N) :
    (10 ^ L) ^ 2 ≤ N ^ 5 := by
  -- squared once more: `10^{4L} ≤ 3^{9L} ≤ 3^{10(L-m)}`
  have hsq :=
    calc ((10 ^ L) ^ 2) ^ 2 = 10000 ^ L := by
          rw [← pow_mul, ← pow_mul, mul_comm L, pow_mul]; norm_num
      _ ≤ 19683 ^ L := Nat.pow_le_pow_left (by norm_num) L
      _ = 3 ^ (9 * L) := by rw [pow_mul]; norm_num
      _ ≤ 3 ^ ((L - m) * 5 * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = ((3 ^ (L - m)) ^ 5) ^ 2 := by rw [pow_mul, pow_mul]
  exact ((Nat.pow_le_pow_iff_left (by norm_num)).mp hsq).trans (Nat.pow_le_pow_left hN 5)

end ThreeSumApsp
