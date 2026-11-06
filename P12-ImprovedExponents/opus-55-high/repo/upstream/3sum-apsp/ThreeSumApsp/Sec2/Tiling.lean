/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec2.Lemma9
import ThreeSumApsp.Sec2.Tiling.Definitions

/-!
# The tiling of the `N × D × N` product

Section 2.3.4. One run of `Full` computes `K` products of shape `N₀ × D × N₀` (Lemma 9).
To multiply an `N × D` matrix `X` by a `D × N` matrix `Y`, cut `X` into row blocks and `Y` into
column blocks of size `N₀`, group the blocks into bands of `K₀ = ⌊√K⌋` blocks, and call a row band
together with a column band a tile. Each tile is one run of `Full`, on a `K₀ × K₀` grid of block
products.

* The numbers: `K₀² ≤ K ≤ 4 K₀²` (`K0_sq_le_K`, `K_le_four_mul_K0_sq`), padding `N ≥ K₀ N₀` to
  a multiple of `K₀ N₀` at most doubles it (`le_padN`, `padN_lt_add_bandSize`, `padN_le_two_mul`),
  and there are at most `4N²/M` tiles, where `N` is the padded size (`card_tiles_mul_M_le`).
* A table of `K₀²` distinct subsets of size `m` exists (`nonempty_layout`; no later proof uses
  this).
* One run computes all the block products of a tile (`Full_bandArray_eq_block_mul`, from Lemma 9),
  and the entry `(XY)[I, J]` is the output of the run on the tile of `(I, J)` at the output string
  of `(I, J)` (`Full_bandArray_eq_mul`).
* Different positions of a tile have different output strings (`outStrOfPos_injective`).
-/


open Finset

namespace ThreeSumApsp

variable {m L : ℕ}

/-! ### The numbers -/

/-- A band has at least one row. -/
theorem bandSize_pos (hmL : m ≤ L) : 0 < bandSize L m :=
  Nat.mul_pos (K0_pos hmL) (N0_pos L m)

/-- The padded size is at least `N`.

NOTE. `m ≤ L` is left implicit in the paper. For `m > L` there is no subset of size `m` and
`K₀ = 0`. -/
theorem le_padN (hmL : m ≤ L) (N : ℕ) : N ≤ padN L m N := by
  have h := Nat.lt_div_mul_add (a := N + bandSize L m - 1) (bandSize_pos hmL)
  unfold padN numBands
  omega

variable (lay : Layout L m)

/-! ### The table of subsets and the matrices of a tile -/

/-- The subsets in the table are distinct, so a sum over the table that selects the subset of the
block product `gh` has one term. -/
theorem sum_table_eq {A : Type*} [AddCommMonoid A]
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (∑ gh', if lay.table gh' = lay.table gh then F gh' else 0) = F gh := by
  simp [lay.table_injective.eq_iff]

variable {N : ℕ}

/-- Section 2.3.4: "In a tile, let X_Q and Y_Q be the row block and the column block of the block
product with subset Q".  For `X_Q`: it is the `g`-th row block of the row band. -/
@[simp]
theorem bandFamilyL_table (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyL lay X β (lay.table (g, h)) = rowBlock lay X (β * K0 L m + g) :=
  sum_table_eq lay _ (g, h)

/-- The matrix `Y_Q` of the block product in position `(g, h)` is the `h`-th column block of the
column band. -/
@[simp]
theorem bandFamilyR_table (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyR lay Y β (lay.table (g, h)) = colBlock lay Y (β * K0 L m + h) :=
  sum_table_eq lay _ (g, h)

variable {Q : Finset (Fin L)}

/-- Section 2.3.4: "and let X_Q = Y_Q = 0 for the other subsets Q."  For `X_Q`. -/
theorem bandFamilyL_eq_zero (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (β : ℕ) (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyL lay X β Q = 0 :=
  sum_eq_zero fun gh _ => by simp_all

/-- Section 2.3.4: "and let X_Q = Y_Q = 0 for the other subsets Q."  For `Y_Q`. -/
theorem bandFamilyR_eq_zero (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (β : ℕ) (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyR lay Y β Q = 0 :=
  sum_eq_zero fun gh _ => by simp_all

/-! ### One run of `Full` for each tile -/

/-- Section 2.3.4: "Then one run of Full computes all K₀² block products of the tile (Lemma 9)".
The tile is that of the row band `β` and the column band `β'`; the block product in position `(g,
h)` of its grid is the product of the row block `β K₀ + g` by the column block `β' K₀ + h`. -/
theorem Full_bandArray_eq_block_mul
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β β' : ℕ)
    (g h : Fin (K0 L m)) (r c : OuterStr L m) :
    Full L (bandArrayL lay X β) (bandArrayR lay Y β')
        (outStrOf (lay.table (g, h)) (lay.table_card (g, h)) r c)
      = (rowBlock lay X (β * K0 L m + g) * colBlock lay Y (β' * K0 L m + h)) r c := by
  rw [bandArrayL, bandArrayR, Full_arrays_eq_mul, bandFamilyL_table, bandFamilyR_table]

variable (I : ℕ)

/-- A row (or column) is recovered from its band, the position of its block in the band and its
position in the block. -/
theorem position_decomp :
    (bandOf L m I * K0 L m + (blockOf lay I : ℕ)) * N0 L m + (offsetOf L m I : ℕ) = I := by
  have hband : bandOf L m I = I / N0 L m / K0 L m := by
    rw [bandOf, bandSize, Nat.mul_comm, Nat.div_div_eq_div_mul]
  have hblock : bandOf L m I * K0 L m + blockOf lay I = I / N0 L m := by
    rw [hband]
    exact Nat.div_add_mod' _ _
  rw [hblock]
  exact Nat.div_add_mod' _ _

/-- Section 2.3.4: "and running it on every tile computes all of XY." The entry `(XY)[I, J]` is the
output of the run on the tile of `(I, J)` at the output string of `(I, J)`. -/
theorem Full_bandArray_eq_mul
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    Full L (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  unfold outStrOfPos
  rw [Full_bandArray_eq_block_mul, Matrix.mul_apply, Matrix.mul_apply,
    ← lay.innerIdx.sum_comp]
  -- Both sides are sums over the `D` inner indices; the summands agree because row `I` is recovered
  -- from its band, block and place in the block, and likewise column `J`.
  grind [rowBlock, colBlock, Equiv.symm_apply_apply, position_decomp, padRows, padCols]

/-- The entry `(XY)[I, J]` as a value of `Mult`, that is, as a sum over leaves (equation (2)). This
is the form in which Section 4 uses the tiling ("by (2) and Lemma 9, (X_Q Y_Q)[w] is the sum of the
products at the leaves contributing to w"). -/
theorem Mult_bandArray_eq_mul (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    Mult (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Lemma7.returns_Mult]
  grind [Full_bandArray_eq_mul]

/-- Every row and every column lies in one of the bands.

NOTE.  `m ≤ L` is left implicit in the paper. -/
theorem bandOf_lt_numBands (hmL : m ≤ L) (N I : ℕ) (hI : I < N) :
    bandOf L m I < numBands L m N := by
  rw [bandOf, Nat.div_lt_iff_lt_mul (bandSize_pos hmL)]
  exact hI.trans_le (le_padN hmL N)

/-! ### The output string of a position -/

/-- Section 2.4.4: the inner set of the output string of a position is "the subset Q of the block
product containing (I, J)". -/
theorem innerSetO_outStrOfPos (J : ℕ) :
    innerSetO (outStrOfPos lay I J) = lay.table (blockOf lay I, blockOf lay J) :=
  innerSetO_outStrOf _ _ _ _

/-- The inner set of the output string of a position has exactly `m` elements. -/
theorem card_innerSetO_outStrOfPos (J : ℕ) :
    (innerSetO (outStrOfPos lay I J)).card = m :=
  innerSetO_outStrOfPos lay I J ▸ lay.table_card _
