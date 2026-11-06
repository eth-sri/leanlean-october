module

public import ThreeSumApsp.Sec2.Levels
public import ThreeSumApsp.Sec2.Lemma10

@[expose] public section

open Finset

namespace ThreeSumApsp

/-- Section 2.3.4: "K₀ := ⌊√K⌋". -/
def K0 (L m : ℕ) : ℕ := Nat.sqrt (K L m)

/-- `N₀ = 3^{L-m}` is positive. -/
theorem N0_pos (L m : ℕ) : 0 < N0 L m := Nat.pow_pos (by decide)

/-- `K₀ = ⌊√binom(L, m)⌋` is positive when `m ≤ L`. -/
theorem K0_pos {L m : ℕ} (h : m ≤ L) : 0 < K0 L m := Nat.sqrt_pos.mpr (Nat.choose_pos h)

/-- The choices that the paper makes once and for all without naming them.

* `hmL`: `m ≤ L`. The paper never states this; it follows from `L = 19m` (Section 2) and from
  `L ≥ 10m` (Section 4). It makes `K₀ ≥ 1`.
* Section 2.3.3: "we index its N₀ rows by the N₀ strings of L - m outer left variables, and its D
  columns by the D strings of m inner left variables", and similarly for a `D × N₀` matrix.
  `rowIdx`, `colIdx` and `innerIdx` say which string indexes which row or column, counted from 0.
* Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
  of the grid, the same in every tile." `table (g, h)` is the subset of the block product of the
  `g`-th row block of a row band and the `h`-th column block of a column band.

Every statement about the tiling holds for every such choice. -/
structure Layout (L m : ℕ) where
  hmL : m ≤ L
  rowIdx : Fin (N0 L m) ≃ OuterStr L m
  colIdx : Fin (N0 L m) ≃ OuterStr L m
  innerIdx : Fin (D m) ≃ InnerStr m
  table : Fin (K0 L m) × Fin (K0 L m) → Finset (Fin L)
  table_card : ∀ gh, (table gh).card = m
  table_injective : Function.Injective table

/-- The number `K₀ N₀` of rows of a row band (Section 2.3.4: a band is `K₀` consecutive blocks of
`N₀` consecutive rows), which is also the number of columns of a column band. -/
def bandSize (L m : ℕ) : ℕ := K0 L m * N0 L m

/-- The number of row bands (and of column bands) after padding: `N / (K₀ N₀)` rounded up. -/
def numBands (L m N : ℕ) : ℕ := (N + bandSize L m - 1) / bandSize L m

/-- Section 2.3.4: "we first pad N to a multiple of K₀ N₀".  The padded size. -/
def padN (L m N : ℕ) : ℕ := numBands L m N * bandSize L m

/-- Section 2.3.4: `X` padded "with zero rows".  Rows are numbered from 0. -/
def padRows {N D' : ℕ} (X : Matrix (Fin N) (Fin D') ℤ) (I : ℕ) (k : Fin D') : ℤ :=
  if h : I < N then X ⟨I, h⟩ k else 0

/-- Section 2.3.4: `Y` padded with "zero columns".  Columns are numbered from 0. -/
def padCols {N D' : ℕ} (Y : Matrix (Fin D') (Fin N) ℤ) (k : Fin D') (J : ℕ) : ℤ :=
  if h : J < N then Y k ⟨J, h⟩ else 0

/-- Section 2.3.4: "Cut X into row blocks of N₀ consecutive rows".  The `B`-th row block (counted
from 0) consists of the rows `B N₀, …, B N₀ + N₀ - 1`. -/
def rowBlock {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (B : ℕ) :
    LeftMat L m :=
  fun r π => padRows X (B * N0 L m + lay.rowIdx.symm r) (lay.innerIdx.symm π)

/-- Section 2.3.4: "and Y into column blocks of N₀ consecutive columns". -/
def colBlock {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (B : ℕ) :
    RightMat L m :=
  fun π c => padCols Y (lay.innerIdx.symm π) (B * N0 L m + lay.colIdx.symm c)

/-- Section 2.3.4: "In a tile, let X_Q and Y_Q be the row block and the column block of the block
product with subset Q, and let X_Q = Y_Q = 0 for the other subsets Q." The row band `β` (counted
from 0) consists of the row blocks `β K₀, …, β K₀ + K₀ - 1`. The subsets in the table are distinct,
so at most one summand is nonzero. -/
def bandFamilyL {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) :
    Finset (Fin L) → LeftMat L m :=
  fun Q => ∑ gh, if lay.table gh = Q then rowBlock lay X (β * K0 L m + gh.1) else 0

/-- The matrices `Y_Q` of a tile; they depend only on its column band `β`. -/
def bandFamilyR {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) :
    Finset (Fin L) → RightMat L m :=
  fun Q => ∑ gh, if lay.table gh = Q then colBlock lay Y (β * K0 L m + gh.2) else 0

/-- Section 2.3.4: "the left input array of a tile depends only on its row band". -/
def bandArrayL {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ) :
    LeftStr L → ℤ :=
  arrayL m (bandFamilyL lay X β)

/-- Section 2.3.4: "and the right one only on its column band". -/
def bandArrayR {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ) :
    RightStr L → ℤ :=
  arrayR m (bandFamilyR lay Y β)

/-- The band that contains row (or column) `I`. -/
def bandOf (L m I : ℕ) : ℕ := I / bandSize L m

/-- The position, within its band, of the block that contains row (or column) `I`. -/
def blockOf {L m : ℕ} (lay : Layout L m) (I : ℕ) : Fin (K0 L m) :=
  ⟨I / N0 L m % K0 L m, Nat.mod_lt _ (K0_pos lay.hmL)⟩

/-- The position of row (or column) `I` within its block. -/
def offsetOf (L m I : ℕ) : Fin (N0 L m) := ⟨I % N0 L m, Nat.mod_lt _ (N0_pos L m)⟩

/-- Section 2.4.4: "Each wanted position (I, J) ∈ W lies in one tile T and is indexed by one output
string of T, the string whose inner set is the subset Q of the block product containing (I, J) and
whose row and column are those of (I, J) within that block product". The tile is the pair
`(bandOf L m I, bandOf L m J)`, and this is the output string. -/
def outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) : OutStr L :=
  outStrOf (lay.table (blockOf lay I, blockOf lay J)) (lay.table_card _)
    (lay.rowIdx (offsetOf L m I)) (lay.colIdx (offsetOf L m J))




/-! ### The numbers -/

/-- A band has at least one row. -/
theorem bandSize_pos {L m : ℕ} (hmL : m ≤ L) : 0 < bandSize L m :=
  Nat.mul_pos (K0_pos hmL) (N0_pos L m)

/-- The padded size is at least `N`.

NOTE. `m ≤ L` is left implicit in the paper. For `m > L` there is no subset of size `m` and
`K₀ = 0`. -/
theorem le_padN {L m : ℕ} (hmL : m ≤ L) (N : ℕ) : N ≤ padN L m N := by
  have := Nat.lt_div_mul_add (a := N + bandSize L m - 1) (bandSize_pos hmL)
  unfold padN numBands
  omega

/-! ### The table of subsets and the matrices of a tile -/

/-- The subsets in the table are distinct, so a sum over the table that selects the subset of the
block product `gh` has one term. -/
theorem sum_table_eq {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (∑ gh', if lay.table gh' = lay.table gh then F gh' else 0) = F gh := by
  simp [lay.table_injective.eq_iff]

/-- Section 2.3.4: "In a tile, let X_Q and Y_Q be the row block and the column block of the block
product with subset Q".  For `X_Q`: it is the `g`-th row block of the row band. -/
@[simp]
theorem bandFamilyL_table {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyL lay X β (lay.table (g, h)) = rowBlock lay X (β * K0 L m + g) :=
  sum_table_eq lay _ (g, h)

/-- The matrix `Y_Q` of the block product in position `(g, h)` is the `h`-th column block of the
column band. -/
@[simp]
theorem bandFamilyR_table {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyR lay Y β (lay.table (g, h)) = colBlock lay Y (β * K0 L m + h) :=
  sum_table_eq lay _ (g, h)

/-- Section 2.3.4: "and let X_Q = Y_Q = 0 for the other subsets Q."  For `X_Q`. -/
theorem bandFamilyL_eq_zero {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (β : ℕ) {Q : Finset (Fin L)} (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyL lay X β Q = 0 :=
  sum_eq_zero fun gh _ => if_neg (hQ gh)

/-- Section 2.3.4: "and let X_Q = Y_Q = 0 for the other subsets Q."  For `Y_Q`. -/
theorem bandFamilyR_eq_zero {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (β : ℕ) {Q : Finset (Fin L)} (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyR lay Y β Q = 0 :=
  sum_eq_zero fun gh _ => if_neg (hQ gh)

/-! ### One run of `Full` for each tile -/

/-- Section 2.3.4: "Then one run of Full computes all K₀² block products of the tile (Lemma 9)".
The tile is that of the row band `β` and the column band `β'`; the block product in position `(g,
h)` of its grid is the product of the row block `β K₀ + g` by the column block `β' K₀ + h`. -/
theorem Full_bandArray_eq_block_mul {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β β' : ℕ)
    (g h : Fin (K0 L m)) (r c : OuterStr L m) :
    Full L (bandArrayL lay X β) (bandArrayR lay Y β')
        (outStrOf (lay.table (g, h)) (lay.table_card (g, h)) r c)
      = (rowBlock lay X (β * K0 L m + g) * colBlock lay Y (β' * K0 L m + h)) r c := by
  rw [bandArrayL, bandArrayR, Full_arrays_eq_mul, bandFamilyL_table, bandFamilyR_table]

/-- A row (or column) is recovered from its band, the position of its block in the band and its
position in the block. -/
theorem position_decomp {L m : ℕ} (lay : Layout L m) (I : ℕ) :
    (bandOf L m I * K0 L m + (blockOf lay I : ℕ)) * N0 L m + (offsetOf L m I : ℕ) = I := by
  have hband : bandOf L m I = I / N0 L m / K0 L m := by
    rw [bandOf, bandSize, Nat.mul_comm, Nat.div_div_eq_div_mul]
  have hblock : bandOf L m I * K0 L m + (blockOf lay I : ℕ) = I / N0 L m := by
    rw [hband]
    exact Nat.div_add_mod' _ _
  rw [hblock]
  exact Nat.div_add_mod' _ _

/-- Section 2.3.4: "and running it on every tile computes all of XY." The entry `(XY)[I, J]` is the
output of the run on the tile of `(I, J)` at the output string of `(I, J)`. -/
theorem Full_bandArray_eq_mul {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    Full L (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  unfold outStrOfPos
  rw [Full_bandArray_eq_block_mul, Matrix.mul_apply, Matrix.mul_apply,
    ← Equiv.sum_comp lay.innerIdx]
  -- Both sides are sums over the `D` inner indices; the summands agree because row `I` is recovered
  -- from its band, block and place in the block, and likewise column `J`.
  refine sum_congr rfl fun k _ => ?_
  simp only [rowBlock, colBlock, Equiv.symm_apply_apply, position_decomp, padRows, padCols,
    I.isLt, J.isLt, dif_pos, Fin.eta]

/-- The entry `(XY)[I, J]` as a value of `Mult`, that is, as a sum over leaves (equation (2)). This
is the form in which Section 4 uses the tiling ("by (2) and Lemma 9, (X_Q Y_Q)[w] is the sum of the
products at the leaves contributing to w"). -/
theorem Mult_bandArray_eq_mul {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    Mult (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Lemma7.returns_Mult]
  exact Full_bandArray_eq_mul lay X Y I J

/-- Every row and every column lies in one of the bands.

NOTE.  `m ≤ L` is left implicit in the paper. -/
theorem bandOf_lt_numBands {L m : ℕ} (hmL : m ≤ L) (N I : ℕ) (hI : I < N) :
    bandOf L m I < numBands L m N := by
  rw [bandOf, Nat.div_lt_iff_lt_mul (bandSize_pos hmL)]
  exact hI.trans_le (le_padN hmL N)

/-! ### The output string of a position -/

/-- Section 2.4.4: the inner set of the output string of a position is "the subset Q of the block
product containing (I, J)". -/
theorem innerSetO_outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) :
    innerSetO (outStrOfPos lay I J) = lay.table (blockOf lay I, blockOf lay J) :=
  innerSetO_outStrOf _ _ _ _

/-- The inner set of the output string of a position has exactly `m` elements. -/
theorem card_innerSetO_outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) :
    (innerSetO (outStrOfPos lay I J)).card = m :=
  innerSetO_outStrOfPos lay I J ▸ lay.table_card _

end ThreeSumApsp
