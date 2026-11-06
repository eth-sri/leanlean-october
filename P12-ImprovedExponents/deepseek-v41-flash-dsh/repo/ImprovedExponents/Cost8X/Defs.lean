module

public import ThreeSumApsp.Sec4.Theorem30
public import ThreeSumApsp.TacticsShort

@[expose] public section

/-!
# The expression (8) with the exact tail of the leaf counts

The preprocessing of Theorem 30 of the paper costs a constant times the expression (8),

  `L m ρ^t/(1 - ρ) N² + N 10^L/(√K N₀)`   (`ThreeSumApsp.cost8`).

Its first summand counts the boxes of all tiles: a tile has at most `(m + 1) ∑_{d ≥ t} β_d` boxes
(`ThreeSumApsp.lemma_29_count`), and the paper bounds the sum by `M ρ^t/(1 - ρ)`. Here the sum is
kept as it is: with `tailX L m t := (∑_{d=t}^{m} β_d)/M`,

  `cost8X L m t N := L m tailX(L, m, t) N² + N 10^L/(√K N₀)`.

This file has the counts in the proof of Theorem 30 against `cost8X` (`cost8X_assembly`). They
replace `ThreeSumApsp.Theorem30.boxes_total`, `boxes_cost` and `cost8_assembly`; the program and
the second summand are not changed.
-/

namespace ImprovedExponents

open ThreeSumApsp Finset

/-- The leaves of order at least `t` of a tile, relative to its number `M` of output entries:
`(∑_{d=t}^{m} β_d)/M`. It takes the place of `ρ^t/(1 - ρ)` in the expression (8). -/
noncomputable def tailX (L m t : ℕ) : ℝ := (∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)) / (M L m : ℝ)

/-- The tail is not negative. -/
theorem tailX_nonneg (L m t : ℕ) : 0 ≤ tailX L m t :=
  div_nonneg (sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The first term of `cost8X` is not negative. -/
theorem cost8X_first_term_nonneg (L m t N : ℕ) :
    0 ≤ (L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2 :=
  mul_nonneg (mul_nonneg tac_positivity (tailX_nonneg L m t)) tac_positivity

/-- The number of boxes of all tiles together is at most `4 (m+1) tailX(L, m, t) N²`: Lemma 29 for
one tile, times the number of tiles. -/
theorem boxes_totalX {L m t N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (ht : t ≤ m)
    (hN : sqrtKN0 L m ≤ N) :
    ((numBands L m N : ℝ)) ^ 2 * ((boxes L m t).card : ℝ)
      ≤ 4 * ((m : ℝ) + 1) * tailX L m t * (N : ℝ) ^ 2 := by
  have hboxes : ((boxes L m t).card : ℝ)
      ≤ ((m : ℝ) + 1) * ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ) := by
    exact_mod_cast lemma_29_count L m t hL ht
  have hsum : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ) :=
    sum_nonneg fun _ _ => Nat.cast_nonneg _
  calc ((numBands L m N : ℝ)) ^ 2 * ((boxes L m t).card : ℝ)
      ≤ (4 * (N : ℝ) ^ 2 / (M L m : ℝ))
          * (((m : ℝ) + 1) * ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)) :=
        mul_le_mul (Theorem30.tiles hm hL hN) hboxes (Nat.cast_nonneg _) tac_positivity
    _ = 4 * ((m : ℝ) + 1) * tailX L m t * (N : ℝ) ^ 2 := by
        unfold tailX
        ring

/-- The first term of `cost8X`: `L` operations for each box of each tile. -/
theorem boxes_costX {L m t N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (ht : t ≤ m)
    (hN : sqrtKN0 L m ≤ N) :
    (L : ℝ) * ((numBands L m N : ℝ) ^ 2 * ((boxes L m t).card : ℝ))
      ≤ 8 * ((L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2) := by
  have htail := tailX_nonneg L m t
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc (L : ℝ) * ((numBands L m N : ℝ) ^ 2 * ((boxes L m t).card : ℝ))
      ≤ (L : ℝ) * (4 * ((m : ℝ) + 1) * tailX L m t * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (boxes_totalX hm hL ht hN) (Nat.cast_nonneg L)
    _ ≤ (L : ℝ) * (4 * (2 * (m : ℝ)) * tailX L m t * (N : ℝ) ^ 2) := by
        -- `m + 1 ≤ 2m`
        gcongr
        linarith
    _ = 8 * ((L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2) := by ring

end ImprovedExponents