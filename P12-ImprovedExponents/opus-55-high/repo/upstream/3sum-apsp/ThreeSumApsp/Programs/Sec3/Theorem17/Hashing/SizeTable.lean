/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Seg
import ThreeSumApsp.Lang.Tactics

/-!
# The table of the sizes of Strassen's recursion

szTable(dst, p, J) writes the sizes p, 4p, …, 4^J p of the matrices of Strassen's recursion, the
list `szList p J`, and changes nothing else (`szTable_spec`, `szTable_meets`).
-/


namespace Light.Sec3

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The table of the sizes: 4^i p for i ≤ J. -/
def szList (p J : ℕ) : List ℤ := (List.range (J + 1)).map fun i : ℕ => ((4 ^ i * p : ℕ) : ℤ)

/-- The table of the sizes has J + 1 entries. -/
@[simp] theorem length_szList (p J : ℕ) : (szList p J).length = J + 1 := by simp [szList]

namespace SzTable

/- The local variables of szTable: the arguments dst, p, J; the exponent; the entry. -/
slots Dst Prime Top Exp Entry

end SzTable

open SzTable in
/-- szTable(dst, p, J). -/
def szTableBody : Stmt :=
  .set Exp (k 0) ;;
  .set Entry (v Prime) ;;
  .store (v Dst) (v Entry) ;;
  .while (v Exp <' v Top) (
    .set Entry (k 4 *' v Entry) ;;
    .set Exp (v Exp +' k 1) ;;
    .store (v Dst +' v Exp) (v Entry))

/-- An upper bound on the number of steps of szTable. -/
def tSzTable (J : ℕ) : ℕ := 17 * J + 11

/-- One more entry of the table. -/
theorem szList_succ (p J : ℕ) :
    szList p (J + 1) = szList p J ++ [((4 ^ (J + 1) * p : ℕ) : ℤ)] := by
  simp [szList, List.range_succ]

/-- The state of szTable before round j: the entries p, …, 4^j p are written, the last of them is in
a local, and no cell outside the table has changed. -/
def SzInv (μ : ℕ → ℤ) (dst p J j : ℕ) (σ : State) : Prop :=
  ∃ μ', σ = ⟨frame [dst, p, J, j, (4 ^ j * p : ℕ)], μ'⟩ ∧ Seg μ' dst (szList p j) ∧
    SameOutside μ μ' dst (J + 1)

variable {μ : ℕ → ℤ} {p J dst : ℕ}

/-- **szTable** writes p, 4p, …, 4^J p and changes nothing else. -/
theorem szTable_spec (hw : (lim.space : ℤ) ≤ lim.word)
    (h4 : (4 : ℤ) ≤ lim.word) (hdst : dst + (J + 1) ≤ lim.space)
    (hp : ((4 ^ J * p : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d szTableBody ⟨frame [dst, p, J], μ⟩ (tSzTable J) fun σ' =>
      Seg σ'.mem dst (szList p J) ∧ SameOutside μ σ'.mem dst (J + 1) := by
  have hfits : ∀ j ≤ J, (4 ^ j * p : ℕ) ≤ lim.word := fun j hj =>
    le_trans (by exact_mod_cast by simp_all [Nat.mul_le_mul_right, Nat.pow_le_pow_right]) hp
  unfold tSzTable
  -- exp := 0; entry := p; dst[0] := entry
  light_set 0
  light_set p
  light_store dst p
  -- while exp < J
  apply Ends.whileBlock (SzInv μ dst p J) J
  ·
    refine ⟨Function.update μ dst p, by simp, ?_, SameOutside.refl.update ⟨by omega, by omega⟩ _⟩
    simpa [szList] using Seg.nil.snoc p
  ·
    rintro j _ hj ⟨μ', rfl, seg, rest⟩
    have hnext := hfits _ hj
    have hfour : 4 ^ (j + 1) * p = 4 * (4 ^ j * p) := by ring
    have haddr : (dst + ((j : ℤ) + 1)).toNat = dst + (szList p j).length := by
      aesop
    -- entry := 4 entry; exp := exp + 1; dst[exp] := entry
    refine ⟨by light_side, by light_side, ?_, Function.update μ' _
      _, ?_, szList_succ p j ▸ seg.snoc _,
      rest.update ⟨by omega, by omega⟩ _⟩
    · rw [hfour] at hnext
      generalize 4 ^ j * p = q at hnext
      light_side
    simp_all [update_frame_setLocal]
  ·
    rintro _ ⟨μ', rfl, seg, rest⟩
    simp_all

/-- **szTable** as a procedure. -/
theorem szTable_meets {q : ℕ} (hP : P[q]? = some szTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word) (hdst : dst + (J + 1) ≤ lim.space)
    (hp : ((4 ^ J * p : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, J] μ (tSzTable J) fun _ μ' =>
      Seg μ' dst (szList p J) ∧ SameOutside μ μ' dst (J + 1) :=
  by grind [Meets.of_body, szTable_spec]
