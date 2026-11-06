/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec4.Theorem30.Memory

/-!
# Theorem 30 in the light language: the tiles and a query against the expressions (8) and L ∑ α_d

Pure arithmetic. The routines of Section 4 have explicit time functions. This file and the next one
show that, under the hypotheses of Theorem 30 (`Hyp30`), time and space of the preprocessing are at
most a constant times the expression (8), and the time of a query is at most a constant times
L ∑_{d ≤ t} α_d.

`Within8 f` says that f is at most a constant times (8). Such bounds can be added, multiplied by a
number and passed to smaller functions. Four quantities are within (8) by the counts in the proof of
Theorem 30: the number 1, the number 10^L of leaves, the work 10^L + L 7^L for each band, and L for
each box of each tile (`within8_one` to `within8_boxes`); the next file adds a fifth, N (L + 1)
(`within8_N_mul`). Every other function is bounded by a multiple of a sum of these: here the time
for all tiles (`within8_tAllTiles`) and the space of their tries (`within8_trieSpace`). For a query
see `exists_tQueryCore_le`.
-/


namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The hypotheses of Theorem 30, and what lies within (8) -/

/-- The hypotheses of Theorem 30 on the parameters. -/
structure Hyp30 (p : Sec2.Par) (t : ℕ) : Prop where
  m_pos : 1 ≤ p.m
  L_ge : 10 * p.m ≤ p.L
  t_le : t ≤ p.m
  N_ge : sqrtKN0 p.L p.m ≤ (p.N : ℝ)

variable {p : Sec2.Par} {t : ℕ}

theorem Hyp30.m_le (h : Hyp30 p t) : p.m ≤ p.L := by
  have := h.L_ge
  omega

theorem Hyp30.L_pos (h : Hyp30 p t) : 1 ≤ p.L := by
  have := h.L_ge
  have := h.m_pos
  omega

namespace Within8

end Within8

variable {m L : ℕ}

/-! ## The tiles -/

/-- For every e ≤ m - t with e ≤ L there is a box with e stars. -/
theorem one_le_length_starBoxes {e : ℕ} (he : e ≤ m - t) (hL : e ≤ L) :
    1 ≤ (starBoxes L m t e).length := by
  grind [head?_nineStrs, starBoxes]

/-- There are at least m - t + 1 boxes: one for each number of stars. -/
theorem succ_le_card_boxes (hL : m ≤ L) : m - t + 1 ≤ (boxes L m t).card := by
  have hsum := List.length_le_sum_of_one_le
    ((List.range (m - t + 1)).map fun e => (starBoxes L m t e).length) fun n hn => by
      grind [one_le_length_starBoxes]
  grind [sum_length_starBoxes, List.length_map, List.length_range]

/-- The time for a tile, in closed form. -/
theorem tTile_eq (L m t : ℕ) : tTile L m t
    = tNewRoot + (m - t + 1) * (tNineFirst L + 120) + (boxes L m t).card * tFillStep L + 60 := by
  have hrounds : ∀ k, ((List.range k).map fun e => tFillList L (starBoxes L m t e).length + 60).sum
      = k * (tNineFirst L + 120)
        + ((List.range k).map fun e => (starBoxes L m t e).length).sum * tFillStep L := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      grind [List.range_succ, tFillList]
  grind [tTile, sum_length_starBoxes]

/-- The time for a tile, and what the loop over the tiles adds to it, is O(L) for each box (Lemma
29). The enumeration of the boxes with e stars is started once for each e ≤ m - t, in O(L) steps
each time; these m - t + 1 starts are paid for by the boxes, of which there are at least m - t + 1
(succ_le_card_boxes). -/
theorem exists_tTile_le : ∃ c : ℕ, ∀ L m t : ℕ, 1 ≤ L → m ≤ L →
    tTile L m t + 120 ≤ c * (L * (boxes L m t).card) := by
  refine ⟨2000, fun L m t hL1 hmL => ?_⟩
  have hcard := succ_le_card_boxes (t := t) hmL
  have hstarts : (m - t + 1) * (tNineFirst L + 120) ≤ (boxes L m t).card * (tNineFirst L + 120) :=
    by simp_all
  rw [tTile_eq]
  simp only [tFillStep, tFillRound, tStarFirst, tHorner, tSumTen, tLookup, tInsert, tNineNext,
    tNewRoot, tNineFirst] at hstarts ⊢
  generalize (boxes L m t).card = b at *
  have hb : b ≤ L * b := Nat.le_mul_of_pos_left _ hL1
  linarith

/-! ## A query -/

/-- The query cost of Theorem 30 is at least L. -/
theorem cast_L_le_costQuery (L m t : ℕ) : (L : ℝ) ≤ costQuery L m t := by
  have hsum : 1 ≤ ∑ d ∈ range (t + 1), (alpha m d : ℝ) := by
    rw [show 1 = (alpha m 0 : ℝ) by simp [alpha]]
    exact single_le_sum (f := fun d => (alpha m d : ℝ)) (by simp) (by simp)
  exact le_mul_of_one_le_right (Nat.cast_nonneg L) hsum

/-- **A query**, once the digits of its output string are known, takes O(L) steps for each number
that it reads. -/
theorem exists_tQueryCore_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ L m t : ℕ, 1 ≤ L → m ≤ L → t ≤ m →
    (tQueryCore L m t : ℝ) ≤ C * costQuery L m t := by
  refine ⟨900, by norm_num, fun L m t hL1 hmL ht => ?_⟩
  have hnat : tQueryCore L m t ≤ 900 * (L * ∑ d ∈ range (t + 1), alpha m d) := by
    have hpos : 1 ≤ alpha m t := Nat.mul_pos (Nat.choose_pos ht) (by positivity)
    rw [tQueryCore, length_lowList ht, length_boxesOf ht, sum_range_succ]
    simp [tScatter, tHorner, tLookup, tNineNext, tNineFirst]
    generalize ∑ d ∈ range t, alpha m d = low
    generalize alpha m t = a at *
    have hlow : low * (60 * L + 30 + (20 * L + 10) + (90 * m + 60) + 90) ≤ low * (360 * L) :=
      Nat.mul_le_mul_left _ (by omega)
    have hboxes : a * (60 * L + 30 + (20 * L + 12) + (90 * m + 60) + 90) ≤ a * (362 * L) :=
      Nat.mul_le_mul_left _ (by omega)
    have hL : L ≤ a * L := Nat.le_mul_of_pos_left _ hpos
    grind
  unfold costQuery
  exact_mod_cast hnat
