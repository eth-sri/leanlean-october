/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Sec2.Recursion
public import ThreeSumApsp.Sec2.Theorem5.Equation6

/-!
# Section 2.4.4: the remaining minutiae and the word size

* Minutiae.  The `K₀²` subsets, the tiles and the positions of `W` number `O(N² / D^{1/18})` in all
  (`minutiae_total_le`), because `K ≤ N` (`K_le_of_D_pow_le`), there are at most `4N²/N₀` tiles
  (`card_tiles_mul_N0_le`), `|W| ≤ 2^{-m} N²`, and `N, N₀ ≥ 2^{m/9}` (`two_rpow_le_of_D_pow_le`,
  `two_rpow_le_N0`).
* Word size.  An entry of an input array is an entry of `X` or `Y` or 0 (`abs_bandArrayL_le`,
  `abs_bandArrayR_le`); an encoded number is a `±1` combination of at most `7^L` of them
  (`abs_encodingL_le`, `abs_encodingR_le`); a value of `Pruned` is a sum of at most `10^L` products
  of two encoded numbers (`abs_Pruned_le`); and `10^L ≤ N²` by equation (6) (`ten_pow_le_sq`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The remaining minutiae -/

/-! ### The word size -/

/-- The subsets in the table are distinct (Section 2.3.4), so a sum over the table that selects the
subset `Q` is one of its terms or 0. -/
private theorem sum_table_eq_zero_or {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (Q : Finset (Fin L)) :
    (∑ gh, if lay.table gh = Q then F gh else 0) = 0
      ∨ ∃ gh, (∑ gh', if lay.table gh' = Q then F gh' else 0) = F gh := by
  by_cases hQ : ∃ gh, lay.table gh = Q
  · obtain ⟨gh, rfl⟩ := hQ
    exact .inr ⟨gh, by simp [lay.table_injective.eq_iff]⟩
  · exact .inl (sum_eq_zero fun gh _ => if_neg (not_exists.mp hQ gh))

/-- Section 2.4.4, word size: "The input entries are of this size, by assumption." Every entry of
the input array of a row band is an entry of `X` or 0.

NOTE.  `0 ≤ A` is needed only when `N = 0`. -/
theorem abs_bandArrayL_le {L m N : ℕ} (lay : Layout L m) {X : Matrix (Fin N) (Fin (D m)) ℤ} {A : ℤ}
    (hA : 0 ≤ A) (hX : ∀ I k, |X I k| ≤ A) (β : ℕ) (u : LeftStr L) :
    |bandArrayL lay X β u| ≤ A := by
  unfold bandArrayL arrayL bandFamilyL
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => rowBlock lay X (β * K0 L m + gh.1)) (innerSetL u)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hA
    · rw [hgh]
      unfold rowBlock padRows
      split_ifs
      · exact hX _ _
      · simpa using hA
  · simpa using hA

/-- Section 2.4.4, word size: "The input entries are of this size, by assumption." Every entry of
the input array of a column band is an entry of `Y` or 0.

NOTE.  `0 ≤ B` is needed only when `N = 0`. -/
theorem abs_bandArrayR_le {L m N : ℕ} (lay : Layout L m) {Y : Matrix (Fin (D m)) (Fin N) ℤ} {B : ℤ}
    (hB : 0 ≤ B) (hY : ∀ k J, |Y k J| ≤ B) (β : ℕ) (v : RightStr L) :
    |bandArrayR lay Y β v| ≤ B := by
  unfold bandArrayR arrayR bandFamilyR
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => colBlock lay Y (β * K0 L m + gh.2)) (innerSetR v)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hB
    · rw [hgh]
      unfold colBlock padCols
      split_ifs
      · exact hY _ _
      · simpa using hB
  · simpa using hB

/-- A combination of the entries of an array, with a product of coefficients 0, 1 or -1 for each
entry, is at most the number of entries times the largest absolute value of an entry. -/
theorem abs_encodeWith_le {α : Type} [Fintype α] {c : Term → α → ℤ} (hc : ∀ lam s, |c lam s| ≤ 1)
    {L : ℕ} {a : (Fin L → α) → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodeWith c τ a| ≤ Fintype.card (Fin L → α) * A := by
  have h := abs_sum_mul_le univ (c := fun u => ∏ ℓ, c (τ ℓ) (u ℓ))
    (fun u _ => abs_prod_le_one _ fun ℓ _ => hc _ _) fun u _ => ha u
  simpa only [encodeWith, mul_comm, card_univ] using h

/-- Section 2.4.4, word size: "Every number in an encoding […] is a ±1 combination of at most 7^L
input entries", so its absolute value is at most `7^L` times the largest absolute value of an input
entry.  For the encoding of `a`. -/
theorem abs_encodingL_le {L : ℕ} {a : LeftStr L → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodingL a τ| ≤ 7 ^ L * A := by
  have h := abs_encodeWith_le abs_phi_le_one ha τ
  rw [card_leftStr] at h
  exact_mod_cast h

/-- Section 2.4.4, word size: "Every number in an encoding […] is a ±1 combination of at most 7^L
input entries".  For the encoding of `b`. -/
theorem abs_encodingR_le {L : ℕ} {b : RightStr L → ℤ} {B : ℤ} (hb : ∀ v, |b v| ≤ B) (τ : Leaf L) :
    |encodingR b τ| ≤ 7 ^ L * B := by
  have h := abs_encodeWith_le abs_psi_le_one hb τ
  rw [card_rightStr] at h
  exact_mod_cast h

end ThreeSumApsp
