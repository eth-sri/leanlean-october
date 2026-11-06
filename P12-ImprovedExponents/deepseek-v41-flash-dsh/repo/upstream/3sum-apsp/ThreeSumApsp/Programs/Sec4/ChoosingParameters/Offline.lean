/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters
public import ThreeSumApsp.Programs.Sec4.Theorem30.Areas
public import ThreeSumApsp.Programs.Sec4.Theorem30.Offline

/-!
# Section 4.4, the offline form: preprocess, then one query for each wanted position

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". Its proof: "The
bound for a set W follows by asking |W| queries." Proof of Theorem 25: "ask one query for each
position of W"; for Corollary 32 the paper uses "the same argument", "With Corollary 31 in place of
Theorem 24".

offline32(N, D, w, U, x, y, wi, wj, out, fr) preprocesses the matrices at x and y (pre31, which uses
the cells from the free pointer fr on) and then asks one query for each of the w positions, whose
rows are at wi and whose columns are at wj; the answers go to out. The arguments are those of the
task `thinTask`. The text `offline32Body`, with the round `offlineAsk32` of its loop, serves all
rational parameters c and θ: they are in the body of the procedure pre31 (`pre31Body`).

A round adds one answer (`offlineAsk32_ends`), with the invariant `Answered` that the offline form
of Theorem 30 uses too, and the routine meets its specification `OfflineSpec32` for all parameters G
(`offline32_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The text -/

/-- The entry (XY)[I, J] for natural numbers I, J (0 outside the matrix). -/
def entryN {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : ℕ) :
    ℤ :=
  if h : I < N ∧ J < N then (X * Y) ⟨I, h.1⟩ ⟨J, h.2⟩ else 0

namespace Offline32

/-- The locals of offline32. The first ten are its arguments: N, D, the number of positions, a bound
that is not used, the addresses of X, of Y, of the rows and of the columns of the wanted positions
and of the output, and the free pointer. Then come the number of the current position and the result
of a call. -/
abbrev Size : ℕ := 0
 abbrev Dim : ℕ := 1
 abbrev Count : ℕ := 2
 abbrev MatX : ℕ := 4
 abbrev MatY : ℕ := 5
 abbrev Rows : ℕ := 6
 abbrev Cols : ℕ := 7
 abbrev Out : ℕ := 8
 abbrev Free : ℕ := 9
 abbrev Pos : ℕ := 10
 abbrev Res : ℕ := 11

end Offline32

open Offline32
/-- One round of offline32: ask the query for the current position and store its answer. -/
def offlineAsk32 : Stmt :=
  .call Proc.query31 [M (v Rows +' v Pos), M (v Cols +' v Pos), v Size, v Dim, v MatX, v MatY,
    v Free] Res ;;
  .store (v Out +' v Pos) (v Res)

open Offline32
/-- offline32(N, D, w, U, x, y, wi, wj, out, fr): preprocess, then ask one query for each wanted
position and store its answer. -/
def offline32Body : Stmt :=
  .call Proc.pre31 [v Size, v Dim, v MatX, v MatY, v Free] Res ;;
  .for Pos (v Count) offlineAsk32

/-! ## What it does -/

/-- **Where the input of offline32 stands**, beyond what `Input31` says: the matrices at aX and aY;
the two lists of indices, which are below N, and the output, all below the free pointer; and the
output meets neither the matrices nor the lists. -/
structure OfflineInput32 {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (aX aY aI aJ out fr : ℕ) (WI WJ : List ℕ) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  rows : SegN μ aI WI
  cols : SegN μ aJ WJ
  length_eq : WJ.length = WI.length
  rows_lt : ∀ I ∈ WI, I < N
  cols_lt : ∀ J ∈ WJ, J < N
  rows_le : aI + WI.length ≤ fr
  cols_le : aJ + WI.length ≤ fr
  out_le : out + WI.length ≤ fr
  out_matX : Apart out WI.length aX (N * D₀)
  out_matY : Apart out WI.length aY (D₀ * N)
  out_rows : Apart out WI.length aI WI.length
  out_cols : Apart out WI.length aJ WI.length

end Light.Sec4
