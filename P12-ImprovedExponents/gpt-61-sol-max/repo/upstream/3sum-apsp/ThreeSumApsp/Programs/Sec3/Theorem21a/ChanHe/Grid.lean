/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Round

/-!
# The reduction from 3SUM to Convolution-3SUM: the loop over the splittings.  row and grid

A step added to the reduction of [CH20, Theorem 5.1], one of the reductions behind Theorem 21(a):
the reduction from 3SUM on one set to the version with three sets, by the first binary digit in
which two labels differ (the label of a value x is x + V).  Below, "round" is the routine of that
name, which handles one splitting; a round of a loop is called so only in the names rowRound and
gridRound and in their lemmas.

* row runs through the splittings `(β, β', v)` for a fixed `β` and adds up the answers of round
  (`row_spec`; a round of its loop is `rowRound_ends`, and what it does to the sum is
  `RowSum.succ`).
* grid runs through `β` and returns 1 if some row has a positive sum (`grid_spec`,
  `gridRound_ends`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe

variable {lim : Limits} {P : Program}

/-! ## The procedures -/

namespace Row

abbrev Beta' := 11

end Row

open Row in
/-- A round of row: the answers for (β, β', false) and (β, β', true) are added to the sum. -/
def rowRound (pRound : ℕ)  :=
  .call pRound
    [v 0, v Beta', k 0,
      v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 12 ;;
  .set 10 (v 10 +' v 12) ;;
  .call pRound
    [v 0, v Beta', k 1,
      v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 12 ;;
  .set 10 (v 10 +' v 12)

open Row in
/-- row(β, nd, val, bt, Λ, A, n, f, cx, fr): sum := 0; a round for each β' < Λ; return the sum. -/
def rowBody (pRound : ℕ)  :=
  .set 10 (k 0) ;;
  .for Beta' (v 4) (rowRound pRound) ;;
  .set 0 (v 10)


/-- A round of grid: if the sum of row β is positive, the answer is 1. -/
def gridRound (pRow : ℕ)  :=
  .call pRow
    [v 10, v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8]
    11 ;;
  .ite (k 0 <' v 11) (.set 9 (k 1)) .skip

/-- grid(nd, val, bt, Λ, A, n, f, cx, fr): answer := 0; a round for each β < Λ; return the
answer. -/
def gridBody (pRow : ℕ)  :=
  .set 9 (k 0) ;;
  .for 10 (v 3) (gridRound pRow) ;;
  .set 0 (v 9)

/-! ## What the two routines share -/

/-- What row and grid assume provides a word for 2Λ + 16, one more level of calls, and what the
routine one level below assumes. -/
theorem GridPre.down {r} {a} {d f e}
    (H : GridPre lim r a f (e + 1) d) :
    2 * a.Λ + 16 ≤ lim.word ∧ d < lim.depth ∧ GridPre lim r a f e (d + 1) := by
  have  := H.V_pos
  have hword := H.ok.word
  have hdepth := H.ok.depth
  have  := Nat.log_lt_self 2 (x := 2 * a.V) (by omega)
  simp only [gridNeed] at hword hdepth
  push_cast at hword
  have  : a.Λ ≤ 2 * a.V := by rw [H.lam, Lam]; omega
  exact ⟨by omega, by omega, H.V_pos, H.m_pos, H.lam, H.primes,
    H.ok.mono (by simp [gridNeed]) (by simp [gridNeed]) (by simp only [gridNeed]; omega)⟩

/-! ## row -/

/-- What is known about the sum after the splittings (β, β', v) with β' < i: it lies between 0 and
2i, and it is positive exactly if one of the answers was yes. -/
structure RowSum (S : ℕ → Bool → Prop) (i : ℕ) (acc : ℤ) : Prop where
  nonneg : 0 ≤ acc
  le : acc ≤ 2 * (i : ℤ)
  pos_iff : 0 < acc ↔ ∃ β' < i, ∃ v, S β' v

/-- Adding the answers for (i, false) and (i, true) takes `RowSum S i` to `RowSum S (i + 1)`. -/
theorem RowSum.succ {S} {i} {acc} (h : RowSum S i acc) :
    RowSum S (i + 1) (acc + flag (S i false) + flag (S i true)) := by
  have  := h.nonneg
  have  := h.le
  have  := flag_mem (S i false)
  have  := flag_mem (S i true)

  refine ⟨by omega, by push_cast; omega, ?_⟩
  rw [(by
    ram_safe
   : (∃ β' < i + 1, ∃ v, S β' v) ↔ (∃ β' < i, ∃ v, S β' v) ∨ S i false ∨ S i true), ← h.pos_iff]
  by_cases hf : S i false <;> by_cases ht : S i true <;>
    simp [flag_of, flag_of_not, hf, ht] <;> omega

section

variable {T : Light.SolverTime} {r : Light.NeedFn} {a : FrontArgs} {d f β pRound : ℕ} {μ : Light.Memory}

/-- The state before round i of the loop of row: the locals are the arguments, the sum, i, and the
last answer; the sum is as `RowSum` says; and below the free pointer only the 3n cells from A have
changed. -/
def RowInv (μ : Light.Memory) (a : FrontArgs) (f β i : ℕ) (σ : State) : Prop :=
  ∃ (acc x : ℤ) (μ' : Light.Memory), RowSum (a.Yes f β) i acc ∧ KeptBut μ μ' a.fr a.A (3 * a.n) ∧
    σ = ⟨frame ((β : ℤ) :: a.vals f ++ [acc, i, x]), μ'⟩

/-- **A round of row** adds the answers for (β, β', false) and (β, β', true) to the sum. -/
theorem rowRound_ends (hRound : RoundSpec lim P pRound T r) (hmem : FrontMem μ a) (hβ : β < a.Λ)
    (H : GridPre lim r a f 1 d) {i} (hi : i < a.Λ) {σ} (hσ : RowInv μ a f β i σ) :
    Ends lim P d (rowRound pRound) σ (2 * tRound T a.n a.V a.m a.np f + 36) fun σ' =>
      σ'.loc Row.Beta' = i ∧ RowInv μ a f β (i + 1)
        { σ' with loc := Function.update σ'.loc Row.Beta' (i + 1) } := by
  obtain ⟨acc, x, μ', hsum, kept, rfl⟩ := hσ
  obtain ⟨hword, hd, H'⟩ := H.down
  have  := flag_mem (a.Yes f β i false)
  have  := flag_mem (a.Yes f β i true)
  have  := hsum.nonneg
  have  := hsum.le
  -- x := round(β, β', 0, nd, val, bt, Λ, A, n, f, cx, fr)
  light_call (hRound a f β i false μ' (hmem.keptBut kept) hβ hi (d + 1) H')
    with _ μ₁ ⟨rfl, kept₁⟩
  -- sum := sum + x
  light_set (acc + flag (a.Yes f β i false))
  -- x := round(β, β', 1, nd, val, bt, Λ, A, n, f, cx, fr)
  light_call (hRound a f β i true μ₁ (hmem.keptBut (kept.trans kept₁)) hβ hi (d + 1) H')
    with _ μ₂ ⟨rfl, kept₂⟩
  -- sum := sum + x
  light_set (acc + flag (a.Yes f β i false) + flag (a.Yes f β i true))
  exact ⟨rfl, _, _, μ₂, hsum.succ, kept.trans (kept₁.trans kept₂),
      by rw [update_frame_setLocal]; rfl⟩

/-- **row** meets its specification. -/
theorem row_spec {p} (hP : P[p]? = some (rowBody pRound))
    (hRound : RoundSpec lim P pRound T r) : RowSpec lim P p T r := by
  intro a f β μ hmem hβ d H
  refine .of_body hP ?_
  have  := H.down.1
  -- sum := 0
  refine Ends.setToThen 0 ?_ (hT := by simp [tRow])
  -- for β' < Λ
  refine Ends.next _ (Ends.for (RowInv μ a f β) a.Λ (2 * tRound T a.n a.V a.m a.np f + 36)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp [tRow]; ring_nf; omega)
  case start =>
    -- The last local has not been written yet and is 0.
    exact ⟨0, 0, μ, ⟨le_rfl, by simp, by simp⟩, .refl,
      by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl⟩
  case round => grind [rowRound_ends]
  case done =>
    rintro _ - ⟨acc, x, μ', hsum, kept, rfl⟩
    -- return the sum
    exact Ends.setTo acc
      ⟨by simpa using hsum.nonneg, by simpa using hsum.le, by simpa using hsum.pos_iff, kept⟩
      (hT := by simp [tRow]; ring_nf; omega)
  case bound =>
    rintro i _ - - ⟨acc, x, μ', -, -, rfl⟩
    simp

end

/-! ## grid -/

section

variable {T : Light.SolverTime} {r : Light.NeedFn} {a : FrontArgs} {d f pRow : ℕ} {μ : Light.Memory}

/-- Some splitting (β, β', v) of row β gives a yes-instance. -/
abbrev FrontArgs.RowYes (a : FrontArgs) f β := ∃ β' < a.Λ, ∃ v, a.Yes f β β' v

/-- The state before round i of the loop of grid: the locals are the arguments, the answer so far,
i, and the sum of the last row; the answer tells whether one of the rows below i had a positive sum;
and below the free pointer only the 3n cells from A have changed. -/
def GridInv (μ : Light.Memory) (a : FrontArgs) (f i : ℕ) (σ : State) : Prop :=
  ∃ (x : ℤ) (μ' : Light.Memory), KeptBut μ μ' a.fr a.A (3 * a.n) ∧
    σ = ⟨frame (a.vals f ++ [flag (∃ β < i, a.RowYes f β), i, x]), μ'⟩

/-- **A round of grid** asks for the sum of row i and sets the answer to 1 if it is positive. -/
theorem gridRound_ends (hRow : RowSpec lim P pRow T r) (hmem : FrontMem μ a)
    (H : GridPre lim r a f 2 d) {i} (hi : i < a.Λ) {σ} (hσ : GridInv μ a f i σ) :
    Ends lim P d (gridRound pRow) σ (tRow T a.n a.V a.m a.np f a.Λ + 18) fun σ' =>
      σ'.loc 10 = i ∧ GridInv μ a f (i + 1)
        { σ' with loc := Function.update σ'.loc 10 (i + 1) } := by
  obtain ⟨x, μ', kept, rfl⟩ := hσ
  obtain ⟨hword, hd, H'⟩ := H.down
  -- sum := row(β, nd, val, bt, Λ, A, n, f, cx, fr)
  light_call (hRow a f i μ' (hmem.keptBut kept) hi (d + 1) H') with sum μ₁ ⟨-, -, hpos, kept₁⟩
  -- if 0 < sum then answer := 1
  refine Ends.iteLast (fun hyes => ?_) fun hno => ?_
  · have hrow := hpos.1 (by simpa using hyes)
    exact Ends.setTo 1 ⟨rfl, sum, μ₁, kept.trans kept₁, by
      rw [update_frame_setLocal, flag_of (Nat.exists_lt_succ_right.2 (Or.inr hrow))]; rfl⟩
  · have hrow := fun h => hno (by simpa using hpos.2 h)
    refine Ends.skip ⟨rfl, sum, μ₁, kept.trans kept₁, ?_⟩
    rw [update_frame_setLocal, flag_congr (Nat.exists_lt_succ_right.trans (or_iff_left hrow))]
    rfl

/-- **grid** meets its specification. -/
theorem grid_spec {p} (hP : P[p]? = some (gridBody pRow)) (hRow : RowSpec lim P pRow T r) :
    GridSpec lim P p T r := by
  intro a f μ hmem d H
  refine .of_body hP ?_
  have  := H.down.1
  -- answer := 0
  refine Ends.setToThen 0 ?_ (hT := by simp [tGrid])
  -- for β < Λ
  refine Ends.next _ (Ends.for (GridInv μ a f) a.Λ (tRow T a.n a.V a.m a.np f a.Λ + 18)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp [tGrid]; ring_nf; omega)
  case start =>
    exact ⟨0, μ, .refl, by
      rw [update_frame_setLocal, ← frame_append_zeros _ 1, flag_of_not (by simp)]; rfl⟩
  case round => grind [gridRound_ends]
  case done =>
    rintro _ - ⟨x, μ', kept, rfl⟩
    -- return the answer
    exact Ends.setTo (flag (∃ β < a.Λ, a.RowYes f β)) ⟨rfl, kept⟩
      (hT := by simp [tGrid]; ring_nf; omega)
  case bound =>
    rintro i _ - - ⟨x, μ', -, rfl⟩
    simp

end

end Light.Sec3.ChanHe
