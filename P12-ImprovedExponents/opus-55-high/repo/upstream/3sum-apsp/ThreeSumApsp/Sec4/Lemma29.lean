/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec4.Boxes

/-!
# Lemma 29: the number of boxes, and their values (Section 4.3)

*The count* (`lemma_29_count`): there are at most `(m+1) ∑_{d=t}^{m} β_d` boxes. A box with `f`
symbols `P₀` or stars is a leaf with `f` symbols `P₀` in which the `e` lowest of them have been
turned into stars, for some `e ≤ f`. So these boxes correspond to the pairs of such a leaf and a
number `e ≤ f`, there are `(f+1) β_{m-f}` of them (`Lemma29.card_filter`), and we sum over
`f ≤ m - t`.

*The values* (`lemma_29_values`): the dynamic program `dpValue`, run on the two encodings of a tile,
returns the value of every box. This is an induction on the number of stars. The boxes without stars
are leaves (`Lemma29.no_stars`), and their values are products of two encoded numbers
(`Lemma29.val_ofLeaf`). Replacing the highest star of a box by the ten terms gives ten boxes with
one star fewer (`lemma_29_split`), whose values add up to the value of the box
(`Lemma29.recurrence`).
-/


open Finset

namespace ThreeSumApsp

variable {m t L : ℕ} {π : Cube L}

/-- Membership in the set of all boxes. -/
@[simp]
theorem mem_boxes : π ∈ boxes L m t ↔ IsBox m t π := by
  simp [boxes]

variable {e : ℕ}

/-- Membership in the set of the boxes with `e` stars. -/
@[simp]
theorem mem_boxesWithStars :
    π ∈ boxesWithStars L m t e ↔ IsBox m t π ∧ (Cube.starLevels π).card = e := by
  simp [boxesWithStars]

/-! ### The count -/

/-- For `f ≤ m ≤ L`, the number of leaves that choose `P₀` at exactly `f` levels is `β_{m-f}`
(Section 2.4.3). -/
lemma card_leaves_P0 {f : ℕ} (hmL : m ≤ L) (hf : f ≤ m) :
    (univ.filter fun τ : Leaf L => (P0Levels τ).card = f).card = beta L m (m - f) := by
  rw [← card_filter_order_eq hmL _ (by omega)]
  simp_all [order]

/-- Proof of Lemma 29, "The count": "There are hence (f+1) binom(L, f) 9^{L-f} = (f+1) β_{m-f} such
boxes", namely boxes with `f` symbols `P₀` or stars, for `f ≤ m - t`. -/
theorem Lemma29.card_filter (L m t f : ℕ) (hmL : m ≤ L) (hf : f ≤ m - t) :
    ((boxes L m t).filter fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card
      = (f + 1) * beta L m (m - f) := by
  -- The pairs of a leaf with `f` symbols `P₀` and a number `e ≤ f`.
  have hpairs : ((univ.filter fun τ : Leaf L => (P0Levels τ).card = f) ×ˢ range (f + 1)).card
      = (f + 1) * beta L m (m - f) := by
    grind [card_product, card_leaves_P0, card_range, mul_comm]
  rw [← hpairs]
  refine card_bij' (fun π _ => (Cube.starsToP0 π, (Cube.starLevels π).card))
    (fun p _ => starLowest p.2 p.1) (fun π hπ => ?_) (fun p hp => ?_) (fun π hπ => ?_)
    fun p hp => ?_
  · -- the pair of such a box is such a pair
    have hf := (mem_filter.1 hπ).2
    simp [mem_product, mem_filter, mem_univ, true_and, mem_range,
      card_P0Levels_starsToP0]
    omega
  · -- the cube of such a pair is such a box: its leaf is the leaf of the pair
    grind [mem_boxes, card_P0Levels_starsToP0, starsToP0_starLowest, isBox_starLowest]
  · -- from a box to its pair and back
    exact (eq_starLowest_starsToP0 π (mem_boxes.1 (mem_filter.1 hπ).1).2).symm
  grind [starsToP0_starLowest, starLevels_starLowest, card_lowest, min_eq_left]

/-- **Lemma 29**, first sentence.  "There are at most (m+1) ∑_{d=t}^{m} β_d boxes." -/
theorem lemma_29_count (L m t : ℕ) (hL : 10 * m ≤ L) (ht : t ≤ m) :
    (boxes L m t).card ≤ (m + 1) * ∑ d ∈ Finset.Icc t m, beta L m d := by
  -- Sort the boxes by the number `f ≤ m - t` of their symbols `P₀` or stars.
  have hsort : (boxes L m t).card = ∑ f ∈ range (m - t + 1),
      ((boxes L m t).filter
        fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card := by
    refine card_eq_sum_card_fiberwise fun π hπ => ?_
    have hi := (mem_boxes.1 (mem_coe.1 hπ)).1
    simp_all
  -- The order `d = m - f` runs from `t` to `m`.
  have hreflect : ∑ f ∈ range (m - t + 1), beta L m (m - f) = ∑ d ∈ Finset.Icc t m, beta L m d := by
    rw [range_eq_Ico, sum_Ico_reflect _ _ (by omega)]
    congr 1
    grind
  -- "summing over f ≤ m - t gives the upper bound on the number of boxes", since `f + 1 ≤ m + 1`
  rw [hsort, ← hreflect, mul_sum]
  refine sum_le_sum fun f hf => ?_
  have hfm := mem_range.1 hf
  rw [Lemma29.card_filter L m t f (by omega) (by omega)]
  exact Nat.mul_le_mul_right _ (by omega)

/-! ### The values -/

/-- Proof of Lemma 29, "The values": "The boxes without stars are the leaves with at most m - t
symbols P₀". -/
theorem Lemma29.no_stars (m t : ℕ) (π : Cube L) :
    π ∈ boxesWithStars L m t 0 ↔ ∃ τ : Leaf L, (P0Levels τ).card ≤ m - t ∧ π = Cube.ofLeaf τ := by
  rw [mem_boxesWithStars]
  constructor
  · rintro ⟨hbox, hstar⟩
    refine ⟨π.starsToP0, ?_,
      π.eq_ofLeaf_of_starLevels_eq_empty (card_eq_zero.1 hstar)⟩
    rw [card_P0Levels_starsToP0]
    exact hbox.1
  · rintro ⟨τ, hτ, rfl⟩
    simp_all [IsBox]

variable (a : LeftStr L → ℤ) (b : RightStr L → ℤ)

/-- Proof of Lemma 29, "The values": "the value of each of them is the product of its two numbers in
the encodings." -/
theorem Lemma29.val_ofLeaf (τ : Leaf L) :
    Cube.val a b (Cube.ofLeaf τ) = Phi τ a * Psi τ b := by
  simp_all [Cube.val, productAt]

/-- Proof of **Lemma 29**, "The values": "For a box π with e ≥ 1 stars, let ℓ be the highest
level at which π has a star. [...] each of these strings is again a box, with e - 1 stars."  The
strings are the `π[ℓ ← λ]`, and `e + 1` stands for the paper's `e`. -/
theorem lemma_29_split (hπ : π ∈ boxesWithStars L m t (e + 1))
    (hne : (Cube.starLevels π).Nonempty) (lam : Term) :
    Cube.replace π ((Cube.starLevels π).max' hne) lam ∈ boxesWithStars L m t e := by
  obtain ⟨⟨hcount, hbelow⟩, hcard⟩ := mem_boxesWithStars.1 hπ
  have hstar : (Cube.starLevels (Cube.replace π ((Cube.starLevels π).max' hne) lam)).card = e := by
    grind [Cube.starLevels_replace, card_erase_of_mem, max'_mem, Nat.add_sub_cancel]
  have hP0 := Cube.P0Levels_replace_subset π ((Cube.starLevels π).max' hne) lam
  refine mem_boxesWithStars.2 ⟨⟨?_, fun k hk k' hk' => ?_⟩, hstar⟩
  · -- One star fewer (`hstar`, `hcard`) and at most one symbol `P₀` more (`hmore`), so (i) stays.
    have hmore := (card_le_card hP0).trans (card_insert_le _ _)
    omega
  grind [Cube.starLevels_replace, lt_of_le_of_ne, le_max']

/-- Proof of Lemma 29, "The values", the displayed recurrence: "val(π) = ∑_λ val(π[ℓ ← λ])", because
"The leaves of π are the leaves of the ten strings π[ℓ ← λ]". It holds for a star at any level `ℓ`
of any cube `π`. -/
theorem Lemma29.recurrence (π : Cube L)
    (ℓ : Fin L) (hℓ : π ℓ = CubeSymbol.star) :
    Cube.val a b π = ∑ lam : Term, Cube.val a b (Cube.replace π ℓ lam) := by
  unfold Cube.val
  rw [← sum_fiberwise _ fun τ => τ ℓ]
  refine sum_congr rfl fun lam _ => sum_congr ?_ fun _ _ => rfl
  grind [Cube.mem_leaves_replace]

/-- **Lemma 29**, second sentence, correctness: "Given the two encodings of a tile, we can compute
the values of all these boxes". The recurrence of the dynamic program of the proof (`dpValue`), run
on the two encodings, returns `val(π)` for every box `π` with `e` stars. That the ten strings π[ℓ ←
λ] are boxes with `e - 1` stars, so that their values can be looked up, is `lemma_29_split`. (For
the time and space bound see `docs/REMARKS.md`, "Section 4: running times".) -/
theorem lemma_29_values (L m t e : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L)
    (hπ : π ∈ boxesWithStars L m t e) :
    dpValue (encodingL a) (encodingR b) e π = Cube.val a b π := by
  induction e generalizing π with
  | zero =>
    obtain ⟨τ, -, rfl⟩ := (Lemma29.no_stars m t π).1 hπ
    rw [Lemma29.val_ofLeaf]
    -- by definition, the leaf of the cube `Cube.ofLeaf τ` is `τ`, and the encodings hold `Φ_τ(a)`
    -- and `Ψ_τ(b)`
    rfl
  | succ e ih =>
    have hne : (Cube.starLevels π).Nonempty :=
      card_pos.1 (by simp_all)
    rw [dpValue, dif_pos hne,
      Lemma29.recurrence a b π _ (Cube.mem_starLevels.1 (max'_mem _ hne))]
    grind [sum_congr, lemma_29_split]
