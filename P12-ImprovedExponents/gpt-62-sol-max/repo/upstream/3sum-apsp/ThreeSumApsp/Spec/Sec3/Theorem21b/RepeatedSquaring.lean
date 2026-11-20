/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import ThreeSumApsp.Util.Asymptotics.PowLittleO
public import ThreeSumApsp.Sec3.Theorem21b.RepeatedSquaring
public import ThreeSumApsp.Spec.Sec3.Problems

/-! Repeated squaring with a single finite sentinel for missing edges. -/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The weight matrix of the graph (0 on the diagonal), row by row, with `INF` where there is no
edge. -/
def weightList (n : ℕ) (INF : ℤ) (ADJ W : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    if q / n = q % n then 0 else if ADJ.getD q 0 = 1 then W.getD q 0 else INF

abbrev sentinel (n U : ℕ) : ℕ := 8 * (n * U)

def squareList (n U : ℕ) (ADJ W : List ℤ) : ℕ → List ℤ
  | 0 => weightList n (sentinel n U) ADJ W
  | t + 1 => minPlusList n (squareList n U ADJ W t) (squareList n U ADJ W t)

@[simp] theorem length_squareList (n U : ℕ) (ADJ W : List ℤ) (t : ℕ) :
    (squareList n U ADJ W t).length = n * n := by
  cases t <;> simp [squareList, weightList, length_minPlusList]

/-- Finite entries are exact and small; a code for infinity has a large positive gap. -/
private structure Code (B H I x : ℤ) (d : WithTop ℤ) : Prop where
  lo : -B ≤ x
  hi : x ≤ H
  gap : d = ⊤ → I - B ≤ x
  eqn : ∀ z : ℤ, d = (z : WithTop ℤ) → x = z ∧ z ≤ B

private theorem Code.add {B H I x y : ℤ} {d e : WithTop ℤ} (h : Code B H I x d)
    (k : Code B H I y e) : Code (2 * B) (2 * H) I (x + y) (d + e) := by
  refine ⟨by linarith [h.lo, k.lo], by linarith [h.hi, k.hi], fun ht => ?_, fun z hz => ?_⟩
  · rcases WithTop.add_eq_top.1 ht with ht | ht
    · linarith [h.gap ht, k.lo]
    · linarith [k.gap ht, h.lo]
  · obtain ⟨a, b, rfl, rfl, rfl⟩ := WithTop.add_eq_coe.1 hz
    obtain ⟨rfl, ha⟩ := h.eqn a rfl
    obtain ⟨rfl, hb⟩ := k.eqn b rfl
    exact ⟨rfl, by linarith⟩

private theorem code_minPlus {n : ℕ} {L : List ℤ} {D : Matrix (Fin n) (Fin n) (WithTop ℤ)}
    {B H I : ℤ} (hgap : 2 * B ≤ I - 2 * B)
    (h : ∀ i j : Fin n, Code B H I (entry n L i j) (D i j)) (i j : Fin n) :
    Code (2 * B) (2 * H) I (entry n (minPlusList n L L) i j) (minPlus D D i j) := by
  rw [entry_minPlusList L L i.isLt j.isLt]
  let a (k : Fin n) := entry n L i k + entry n L k j
  let b (k : Fin n) := D i k + D k j
  have hab k : Code (2 * B) (2 * H) I (a k) (b k) := (h i k).add (h k j)
  have hinf k : minPlus D D i j ≤ b k := Finset.inf_le (Finset.mem_univ k)
  obtain ⟨k, hk, hm⟩ := exists_minPlusEntry_eq i.pos L L i j
  lift k to Fin n using hk
  change minPlusEntry n L L i j = a k at hm
  refine ⟨hm.trans_ge (hab k).lo, hm.trans_le (hab k).hi,
    fun hz => hm.trans_ge ((hab k).gap (top_le_iff.1 (hz ▸ hinf k))), fun z hz => ?_⟩
  obtain ⟨k₀, -, h₀⟩ := Finset.exists_mem_eq_inf Finset.univ ⟨i, Finset.mem_univ i⟩ b
  obtain ⟨ha, hzB⟩ := (hab k₀).eqn z (h₀.symm.trans hz)
  refine ⟨le_antisymm ((minPlusEntry_le _ _ _ _ _ k₀.isLt).trans_eq ha) ?_, hzB⟩
  rw [hm]
  cases hk : b k with
  | top => exact hzB.trans (hgap.trans ((hab k).gap hk))
  | coe w => rw [(hab k).eqn w hk |>.1]; exact WithTop.coe_le_coe.1 (hz ▸ hk ▸ hinf k)

private theorem pow_clog_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  rcases eq_or_lt_of_le hn with rfl | h
  · decide
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) h
  change 2 ^ (Nat.clog 2 n - 1) < n at hp
  have hpos := Nat.clog_pos (by decide : 1 < 2) h
  rw [show Nat.clog 2 n = Nat.clog 2 n - 1 + 1 by omega, pow_succ']
  omega

private theorem pow_le {n t : ℕ} (hn : 1 ≤ n) (ht : t ≤ Nat.clog 2 n) : (2 : ℤ) ^ t ≤ 2 * n := by
  exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) ht).trans (pow_clog_le hn)

variable {n U : ℕ} {ADJ W : List ℤ}

private theorem code_squareList (hW : AbsLe W U) {t : ℕ} (ht : t ≤ Nat.clog 2 n) (i j : Fin n) :
    Code (2 ^ t * (U : ℤ)) (2 ^ t * (sentinel n U : ℕ)) (sentinel n U : ℕ)
      (entry n (squareList n U ADJ W t) i j) (minPlusSquares (graphOf n ADJ W) t i j) := by
  induction t generalizing i j with
  | zero =>
    rw [squareList, entry, weightList, List.getD_map_range _ (Nat.mul_add_lt_mul i.isLt j.isLt),
      Nat.mul_add_div_of_lt j.isLt, Nat.mul_add_mod_of_lt j.isLt]
    have hw := abs_le.1 (hW.abs_getD_le (by positivity) (i.val * n + j.val))
    have hu : (U : ℤ) ≤ (sentinel n U : ℕ) := by
      have := Nat.mul_le_mul_right U i.pos
      push_cast
      omega
    simp only [minPlusSquares, weightMatrix, Matrix.of_apply, graphOf, Fin.ext_iff, pow_zero, one_mul]
    split_ifs <;> constructor <;> simp_all <;> omega
  | succ t ih =>
    have hp := pow_le i.pos ht
    rw [pow_succ', mul_assoc, mul_assoc]
    apply code_minPlus (h := ih (Nat.le_of_succ_le ht))
    rw [pow_succ'] at hp
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg U : (0 : ℤ) ≤ U)]

abbrev apspBound (n U : ℕ) : ℕ := 2 * n * sentinel n U

theorem abs_squareList_le (hW : AbsLe W U) {t : ℕ} (ht : t ≤ Nat.clog 2 n) :
    AbsLe (squareList n U ADJ W t) (apspBound n U) := by
  intro z hz
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul (length_squareList n U ADJ W t ▸ hq)
  rw [← List.getD_eq_getElem _ 0 hq, ← entry, abs_le]
  have h := code_squareList (ADJ := ADJ) hW ht ⟨a, ha⟩ ⟨b, hb⟩
  have hp := pow_le (by omega : 1 ≤ n) ht
  have hB : (U : ℤ) ≤ (sentinel n U : ℕ) := by
    have := Nat.mul_le_mul_right U (show 1 ≤ n by omega)
    push_cast
    omega
  have hP := mul_le_mul_of_nonneg_right hp (show (0 : ℤ) ≤ (sentinel n U : ℕ) by positivity)
  have hQ := mul_le_mul_of_nonneg_left hB (show (0 : ℤ) ≤ 2 ^ t by positivity)
  have hlo := h.lo
  have hhi := h.hi
  push_cast at hP hQ hlo hhi ⊢
  exact ⟨by linarith, by linarith⟩

theorem squareList_distances (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) :
    ∃ dist : Fin n → Fin n → WithTop ℤ, IsDistanceMatrix (graphOf n ADJ W) dist ∧ ∀ i j : Fin n,
      (dist i j = ⊤ → 2 * ((n * U : ℕ) : ℤ) < entry n (squareList n U ADJ W (Nat.clog 2 n)) i j) ∧
      ∀ z : ℤ, dist i j = (z : WithTop ℤ) →
        entry n (squareList n U ADJ W (Nat.clog 2 n)) i j = z ∧ z ≤ 2 * ((n * U : ℕ) : ℤ) := by
  refine ⟨_, theorem_21b_repeated_squaring _ hc, fun i j => ?_⟩
  have h := code_squareList (ADJ := ADJ) hW le_rfl i j
  have hp := mul_le_mul_of_nonneg_right (pow_le i.pos le_rfl) (Nat.cast_nonneg U : (0 : ℤ) ≤ U)
  have hB : (0 : ℤ) < ((n * U : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos i.pos hU
  push_cast at hB ⊢
  exact ⟨fun hz => by have := h.gap hz; push_cast at this; linarith,
    fun z hz => ⟨(h.eqn z hz).1, by linarith [(h.eqn z hz).2]⟩⟩

end ThreeSumApsp.Spec
