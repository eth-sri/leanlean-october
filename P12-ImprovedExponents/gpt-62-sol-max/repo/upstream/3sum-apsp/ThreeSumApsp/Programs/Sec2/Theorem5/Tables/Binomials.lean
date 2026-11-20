/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.Symbolic
import ThreeSumApsp.Lang.Lib.Rect
public import ThreeSumApsp.Lang.Lib.Pass

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-! A single row of Pascal's triangle suffices: update it in place from right to left. -/

@[expose] public section

namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Binom

registers [Levels, Size, Addr, Row, Place, Tail]

end Binom

open Binom

abbrev binomCell : Expr := v Addr +' (v Levels -' v Place)
abbrev binomEntry : Stmt := .store binomCell (M binomCell +' M (binomCell -' k 1))

/-- binom(L, m, pas). -/
def binomBody : Stmt :=
  .store (v Addr) (k 1) ;; .set Tail (v Addr +' k 1) ;;
  pass Place (v Levels) (v Tail) (k 0) ;;
  .for Row (v Levels) (.for Place (v Levels) binomEntry) ;;
  .set Levels (M (v Addr +' v Size))

/-- Entries to the right of p already belong to the next row. -/
private def Mixed (μ : ℕ → ℤ) (L pas i p : ℕ) (ν : ℕ → ℤ) : Prop :=
  (∀ j ≤ L, ν (pas + j) = if p < j then (((i + 1).choose j : ℕ) : ℤ) else (i.choose j : ℕ)) ∧
    SameOutside μ ν pas (L + 2)

/-- One more entry has been replaced. -/
private theorem Mixed.step {μ μ' : ℕ → ℤ} {L pas i p : ℕ} (h : Mixed μ L pas i (p + 1) μ')
    (hp : p + 1 ≤ L) :
    Mixed μ L pas i p (Function.update μ' (pas + (p + 1)) ((i + 1).choose (p + 1) : ℕ)) := by
  refine ⟨fun j hj => ?_, h.2.update ⟨by omega, by omega⟩ _⟩
  by_cases hjp : j = p + 1
  · simp_all
  · rw [Function.update_of_ne (by omega), h.1 j hj]
    omega

variable {μ : ℕ → ℤ} {L m pas : ℕ}

/-- **binom** returns (L choose m) and changes no cell outside the L + 2 cells from pas. -/
theorem binom_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hm : m ≤ L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d binomBody ⟨frame [L, m, pas], μ⟩ (30 * (L + 1) ^ 2) fun σ' =>
      σ'.loc 0 = (L.choose m : ℕ) ∧ SameOutside μ σ'.mem pas (L + 2) := by
  light_facts std
  unfold binomBody
  light_step
  light_set ((pas + 1 : ℕ) : ℤ)
  refine Ends.next _ (Ends.pass (x := Levels) (y := Tail) (dst := pas + 1) (n := L) (fun _ => 0)
    (by intros; light_side) ?_ std.space_le (by omega) rfl rfl (hT := le_rfl)) (by light_time)
  simp only [update_frame_setLocal]
  let l : List ℤ := [L, m, pas, 0, L, (pas + 1 : ℕ)]
  refine Ends.next _ (Ends.forRect (fun _ : Unit => frame l) (fun i j _ ν => Mixed μ L pas i (L - j) ν)
    (n := L) (m := L) (b := binomEntry.blockCost) () ?_ (by omega) (by omega) (by intros; rfl)
    (by intros; rfl) ?_ ?_ ?_ (hT := le_rfl)) (by light_time)
  · refine ⟨fun j hj => ?_, ((SameOutside.refl.update ⟨by omega, by omega⟩ 1).trans
        ((sameOutside_wrote le_rfl).mono (by omega) (by omega)))⟩
    rw [Nat.sub_zero, ite_eq_right (by omega)]
    cases j with
    | zero => rw [wrote_rest (Or.inl (by omega)), Nat.add_zero, Function.update_self]; rfl
    | succ j => rw [← Nat.add_assoc, Nat.add_right_comm, wrote_done (by omega)]; rfl
  · intro i j u ν hi hj I
    obtain ⟨p, hp⟩ : ∃ p, L - j = p + 1 := ⟨L - j - 1, by omega⟩
    rw [hp] at I
    have habove := I.1 (p + 1) (by omega)
    have hleft := I.1 p (by omega)
    rw [ite_eq_right (by omega)] at habove hleft
    have hc := Nat.choose_succ_succ' i p
    have hb : (i + 1).choose (p + 1) ≤ 2 ^ L :=
      (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) hi)
    have haddr : ((pas : ℤ) + ((L : ℤ) - j) - 1).toNat = pas + p := by omega
    have haddr' : ((pas : ℤ) + ((L : ℤ) - j)).toNat = pas + (p + 1) := by omega
    rw [show L - (j + 1) = p by omega]
    simp only [rectLoc, update_frame_setLocal, binomEntry]
    refine Ends.storeTo (pas + (p + 1)) ((i + 1).choose (p + 1) : ℕ) ⟨(), rfl, I.step (by omega)⟩
      (he := by light_side [binomCell, l, haddr, haddr', habove, hleft, hc]) (hT := le_rfl)
  · intro i u ν hi I
    refine ⟨fun j hj => ?_, I.2⟩
    cases j with
    | zero => simpa using I.1 0 (Nat.zero_le _)
    | succ j => simp_all [I.1 _ hj]
  · intro u j ν I
    have hr := I.1 m hm
    simp only [Nat.sub_zero, ite_eq_right (not_lt.mpr hm)] at hr
    simp only [rectLoc, update_frame_setLocal]
    light_step using l, hr
    exact ⟨by simp [l], I.2⟩

/-- **The specification that the callers of binom assume.** -/
theorem binom_entry (std : Std lim) (hP : P[pBinom]? = some binomBody) {c : ℕ} (hc : 30 ≤ c) :
    BinomSpec lim P c :=
  fun _ _ _ _ hsp hm hw _ _ => .mono_const (.of_body hP (binom_spec std hsp hm hw)) hc

end Light.Sec2
