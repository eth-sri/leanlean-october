/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import Mathlib.Data.Int.SuccPred

/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The pure model: the powers 1, b, …, b^(L-1). -/
def powList (b L : ℕ) : List ℤ := (List.range L).map fun j => ((b ^ j : ℕ) : ℤ)

@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (powList b L).length) :
    (powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [powList]

namespace PowTable

/-- The local variables of powTable: the arguments dst, L and b, the exponent j, and the power b^j.
-/
registers [Dest, Len, Base, Expo, Power]

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

/-- The body of powTable writes the powers of b and changes nothing else, whatever its local
variables hold apart from the three arguments. -/
theorem powTable_ends {μ : ℕ → ℤ} {dst L b : ℕ} (e p : ℤ) (t : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d powTableBody ⟨frame (dst :: L :: b :: e :: p :: t), μ⟩ (powTableTime L) fun σ' =>
      Seg σ'.mem dst (powList b L) ∧ SameOutside μ σ'.mem dst L := by
  have h1 : (1 : ℤ) ≤ lim.word := by simpa using hpow 0 (Nat.zero_le _)
  unfold powTableBody powTableTime
  -- p := 1
  light_step
  let f (j : ℕ) : ℤ := (b ^ j : ℕ)
  refine Ends.forShape (fun j z ν => ⟨frame (dst :: L :: b :: j :: z :: t), ν⟩)
    (fun j z ν => z = f j ∧ ν = wrote μ dst f j) L powTableRound.blockCost 1
    ⟨by simp [f], wrote_zero.symm⟩ ?_ ?_ (hT := by light_time [powTableRound])
  · rintro j z ν hj ⟨rfl, rfl⟩
    have hf : f (j + 1) ≤ lim.word := hpow _ (by omega)
    have hval : f j * b = f (j + 1) := by simp [f, pow_succ]
    have hn : 0 ≤ f (j + 1) := by positivity
    unfold powTableRound
    light_store (dst + j) (f j)
    light_set (f (j + 1)) using hval
    exact ⟨_, _, rfl, rfl, wrote_succ⟩
  · rintro _ ν ⟨-, rfl⟩
    exact ⟨seg_wrote (length_powList b L) (fun _ => getElem_powList), sameOutside_wrote le_rfl⟩

end Light
