/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.Memory

/-!
# The pruned recursion (Section 2.4.2), recursive as printed

pruned(n, ea, eb, l, len, out, sp, p10).  The set S passed to the call is the increasing list of len
codes at l; ea and eb are the addresses at which the parts of the two encodings below the current
vertex begin; the array that is returned is written to the len cells from out, in the order of the
list.  The frame of a call with n ≥ 1 starts at sp: 11 cells for the bounds of the ten slices, len
cells for the codes without their first digits, len cells for the list of a child, len cells for the
values of a child.

(1) If n = 0: the product of the two numbers looked up, for each code of the list
    (`prunedBody_ends_zero`).
(2) The slices S_z are segments of the list (segBounds); S_λ is the merge of the slice at z_ij and
    the slice at z₀ (`prunedSlice_ends`, then union).
(3) For each term λ with S_λ ≠ ∅: the recursive call.
(4) The slice of the result at z_ij is C_{P_ij} restricted to S_{z_ij} (pick, writing); the slice at
    z₀ is the sum of the ten C_λ restricted to S_{z₀} (pick, adding, after the cells have been
    cleared).  Steps (3) and (4) for one term are `prunedChild_ends`.

One round of the loop over the ten terms is `prunedRound_ends`; the case n ≥ 1 is
`prunedSetup_ends` followed by the loop (`prunedBody_ends_succ`); `PrunedCtx.entry` is the induction
on n.  What the calls do to the memory is proved in Pruned/Memory.lean; here each call is one step.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace PrunedLocal

/-- The number n of levels that are left. -/
abbrev NN : ℕ := 0
/-- Where the part of the first encoding below the current vertex begins. -/
abbrev PA : ℕ := 1
/-- Where the part of the second encoding below the current vertex begins. -/
abbrev PB : ℕ := 2
/-- The list of the codes that are passed to the call. -/
abbrev PL : ℕ := 3
/-- The length of that list. -/
abbrev LEN : ℕ := 4
/-- Where the values are written. -/
abbrev OUT : ℕ := 5
/-- The frame of the call; it begins with the bounds of the ten slices. -/
abbrev SP : ℕ := 6
/-- The table of the powers of ten. -/
abbrev P10 : ℕ := 7
/-- 10^(n-1); for n = 0 the product of the two numbers looked up. -/
abbrev PW : ℕ := 8
/-- Results of calls that are not used. -/
abbrev RES : ℕ := 9
/-- The codes without their first digits. -/
abbrev COD : ℕ := 10
/-- The list of the child. -/
abbrev CH : ℕ := 11
/-- The values of the child. -/
abbrev VAL : ℕ := 12
/-- The frame of the child. -/
abbrev NXT : ℕ := 13
/-- The position of the slice at z₀. -/
abbrev Z0 : ℕ := 14
/-- The length of the slice at z₀. -/
abbrev NZ0 : ℕ := 15
/-- The term λ. -/
abbrev LAM : ℕ := 16
/-- The position of the slice at the output variable of λ. -/
abbrev POS : ℕ := 17
/-- The length of that slice (0 for λ = P₀). -/
abbrev NPOS : ℕ := 18
/-- The length of the list of the child. -/
abbrev NCH : ℕ := 19

end PrunedLocal

open PrunedLocal

/-- Step (2), first half: the position and the length of the slice at the output variable of λ. -/
def prunedSlice : Stmt :=
  .set POS (M (v SP +' v LAM)) ;;
  .ite (v LAM <' k 9) (.set NPOS (M (v SP +' v LAM +' k 1) -' v POS)) (.set NPOS (k 0))

/-- Steps (3) and (4) for a term λ with S_λ ≠ ∅. -/
def prunedChild : Stmt :=
  .call pPruned [v NN -' k 1, v PA +' v LAM *' v PW, v PB +' v LAM *' v PW, v CH, v NCH, v VAL,
    v NXT, v P10] RES ;;
  .call pPick [v COD +' v POS, v NPOS, v CH, v NCH, v VAL, v OUT +' v POS, k 0] RES ;;
  .call pPick [v COD +' v Z0, v NZ0, v CH, v NCH, v VAL, v OUT +' v Z0, k 1] RES

/-- One round of the loop over the ten terms. -/
def prunedRound : Stmt :=
  prunedSlice ;;
  .call pUnion [v COD +' v POS, v NPOS, v COD +' v Z0, v NZ0, v CH] NCH ;;
  .ite (k 0 <' v NCH) prunedChild .skip ;;
  .set LAM (v LAM +' k 1)

/-- What a call with n ≥ 1 does before the loop: the slices are found, the parts of the frame get
their addresses, and the cells of the slice at z₀ are cleared. -/
def prunedSetup : Stmt :=
  .set PW (M (v P10 +' (v NN -' k 1))) ;;
  .call pSegBounds [v PL, v LEN, v PW, v SP] RES ;;
  .set COD (v SP +' k 11) ;;
  .set CH (v COD +' v LEN) ;;
  .set VAL (v CH +' v LEN) ;;
  .set NXT (v VAL +' v LEN) ;;
  .set Z0 (M (v SP +' k 9)) ;;
  .set NZ0 (v LEN -' v Z0) ;;
  .call pFill [v OUT +' v Z0, v NZ0, k 0] RES ;;
  .set LAM (k 0)

/-- pruned(n, ea, eb, l, len, out, sp, p10). -/
def prunedBody : Stmt :=
  .ite (v NN =' k 0)
    (.set PW (M (v PA) *' M (v PB)) ;;
     .call pFill [v OUT, v LEN, v PW] RES)
    (prunedSetup ;;
     .while (v LAM <' k 10) prunedRound)

/-! ## What the proofs assume -/

variable {lim : Limits} {P : Program} {h d n t : ℕ} {x : PrunedArgs} {μ μ' : ℕ → ℤ}

/-! ## Step (1) -/

/-! ## One round of the loop -/

/-! ## The case n ≥ 1 -/

/-! ## The recursion -/

end Light.Sec2
