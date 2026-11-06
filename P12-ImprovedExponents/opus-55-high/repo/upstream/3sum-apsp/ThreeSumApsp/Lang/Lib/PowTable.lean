/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Seg
import ThreeSumApsp.Lang.Tactics
import Mathlib.Data.Int.SuccPred

/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/


namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The pure model: the powers 1, b, …, b^(L-1). -/
def powList (b L : ℕ) : List ℤ := (List.range L).map fun j => ((b ^ j : ℕ) : ℤ)

@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (powList b L).length) :
    (powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [powList]

namespace PowTable

/- The local variables of powTable: the arguments dst, L and b, the exponent j, and the power b^j.
-/
slots Dest Len Base Expo Power

end PowTable

open PowTable

/-- One round: dst[j] := p; p := p * b. -/
def powTableRound : Stmt :=
  .store (v Dest +' v Expo) (v Power) ;;
  .set Power (v Power *' v Base)

/-- powTable(dst, L, b): p := 1; for j < L: dst[j] := p; p := p * b. -/
def powTableBody : Stmt :=
  .set Power (k 1) ;;
  .for Expo (v Len) powTableRound

/-- The time of powTable. -/
def powTableTime (L : ℕ) : ℕ := 17 * L + 8

/-- The state before round j: p = b^j, the first j cells hold the powers up to b^(j-1), and no cell
outside the L cells from dst has changed.  The list t holds the local variables after the five of
powTable. -/
def PowTable.Filled (μ : ℕ → ℤ) (dst L b : ℕ) (t : List ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame (dst :: L :: b :: j :: ((b ^ j : ℕ) : ℤ) :: t), μ'⟩ ∧
    (∀ i < j, μ' (dst + i) = ((b ^ i : ℕ) : ℤ)) ∧ SameOutside μ μ' dst L

/-- The body of powTable writes the powers of b and changes nothing else, whatever its local
variables hold apart from the three arguments. -/
theorem powTable_ends {μ : ℕ → ℤ} {dst L b : ℕ} (e p : ℤ) (t : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d powTableBody ⟨frame (dst :: L :: b :: e :: p :: t), μ⟩ (powTableTime L) fun σ' =>
      Seg σ'.mem dst (powList b L) ∧ SameOutside μ σ'.mem dst L := by
  have h1 : 1 ≤ lim.word := by simpa using hpow 0 (Nat.zero_le _)
  unfold powTableBody powTableTime
  -- p := 1
  light_set 1
  -- for j < L
  refine Ends.for (Filled μ dst L b t) L powTableRound.blockCost ?start ?round ?done ?bound
    (hT := by light_time [powTableRound])
  case start => exact ⟨μ, by simp [update_frame_setLocal], by omega, .refl⟩
  case bound =>
    rintro j _ - - ⟨μ', rfl, -⟩
    light_side
  case done =>
    rintro _ - ⟨μ', rfl, powers, same⟩
    exact ⟨fun i hi => by aesop, same⟩
  case round =>
    rintro j _ hj - ⟨μ', rfl, powers, same⟩
    have hfits : b ^ (j + 1) ≤ lim.word := by simp_all
    unfold powTableRound
    -- dst[j] := p
    light_store (dst + j) (b ^ j)
    -- p := p * b
    light_set (b ^ (j + 1)) using ← pow_succ
    refine ⟨by simp, Function.update μ' (dst + j) (b ^ j), by simp [update_frame_setLocal],
      fun i hi => ?_, by light_keep⟩
    grind
