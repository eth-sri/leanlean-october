/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Tactics

/-!
# The table of the sizes of Strassen's recursion

szTable(dst, p, J) writes the sizes p, 4p, …, 4^J p of the matrices of Strassen's recursion, the
list `szList p J`, and changes nothing else (`szTable_spec`, `szTable_meets`).
-/

@[expose] public section

namespace Light.Sec3

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The table of the sizes: 4^i p for i ≤ J. -/
def szList p J := (List.range (J + 1)).map fun i : ℕ => ((4 ^ i * p : ℕ) : ℤ)

/-- The table of the sizes has J + 1 entries. -/
@[simp] theorem length_szList p J : (szList p J).length = J + 1 := by simp [szList]


/-- szTable(dst, p, J). -/
def szTableBody  :=
  .set 3 (k 0) ;;
  .set 4 (v 1) ;;
  .store (v 0) (v 4) ;;
  .while (v 3 <' v 2) (
    .set 4 (k 4 *' v 4) ;;
    .set 3 (v 3 +' k 1) ;;
    .store (v 0 +' v 3) (v 4))

/-- An upper bound on the number of steps of szTable. -/
def tSzTable J := 17 * J + 11

/-- One more entry of the table. -/
theorem szList_succ p J :
    szList p (J + 1) = szList p J ++ [((4 ^ (J + 1) * p : ℕ) : ℤ)] := by
  simp [szList, List.range_succ]

/-- The state of szTable before round j: the entries p, …, 4^j p are written, the last of them is in
a local, and no cell outside the table has changed. -/
def SzInv (μ : Light.Memory) (dst p J j : ℕ) (σ : State) : Prop :=
  ∃ μ', σ = ⟨frame [dst, p, J, j, (4 ^ j * p : ℕ)], μ'⟩ ∧ Seg μ' dst (szList p j) ∧
    SameOutside μ μ' dst (J + 1)

/-- **szTable** writes p, 4p, …, 4^J p and changes nothing else. -/
theorem szTable_spec {μ} {dst p J} (hw : (lim.space : ℤ) ≤ lim.word)
    (h4 : (4 : ℤ) ≤ lim.word) (hdst : dst + J + 1 ≤ lim.space)
    (hp : ((4 ^ J * p : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d szTableBody ⟨frame [dst, p, J], μ⟩ (tSzTable J) fun σ' =>
      Seg σ'.mem dst (szList p J) ∧ SameOutside μ σ'.mem dst (J + 1) := by

  unfold tSzTable
  -- exp := 0; entry := p; dst[0] := entry
  light_set (0 : ℕ)
  light_set p
  light_store dst p
  -- while exp < J
  refine Ends.whileBlock (SzInv μ dst p J) J ?start ?round ?done
  case start =>
    refine ⟨Function.update μ dst p, by simp, ?_, SameOutside.refl.update ⟨by omega, by omega⟩ _⟩
    simpa [szList] using Seg.nil (μ := μ) (a := dst).snoc p
  case round =>
    rintro j _ hj ⟨μ', rfl, seg, rest⟩
    have hnext := (fun j hj =>
      le_trans (by gcongr) hp
     : ∀ j ≤ J, ((4 ^ j * p : ℕ) : ℤ) ≤ lim.word) (j + 1) hj
    have hfour : 4 ^ (j + 1) * p = 4 * (4 ^ j * p) := by ring
    have  : ((dst : ℤ) + ((j : ℤ) + 1)).toNat = dst + (szList p j).length := by
      rw [length_szList]
      omega
    -- entry := 4 entry; exp := exp + 1; dst[exp] := entry
    refine ⟨by light_side, by light_side, ?_, Function.update μ' (dst + (szList p j).length)
      ((4 ^ (j + 1) * p : ℕ) : ℤ), ?_, szList_succ p j ▸ seg.snoc _,
      rest.update ⟨by omega, by rw [length_szList]; omega⟩ _⟩
    · rw [hfour] at hnext
      generalize 4 ^ j * p = q at hnext
      light_side
    · ram_arith [update_frame_setLocal]
  case done =>
    rintro _ ⟨μ', rfl, seg, rest⟩
    exact ⟨by light_side, by light_side, seg, rest⟩

/-- **szTable** as a procedure. -/
theorem szTable_meets {μ} {q dst p J} (hP : P[q]? = some szTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word) (hdst : dst + J + 1 ≤ lim.space)
    (hp : ((4 ^ J * p : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, J] μ (tSzTable J) fun _ μ' =>
      Seg μ' dst (szList p J) ∧ SameOutside μ μ' dst (J + 1) :=
  Meets.of_body hP (szTable_spec hw h4 hdst hp)

end Light.Sec3
