/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# A binomial coefficient, by Pascal's triangle

Section 2.3.4 needs the number K = (L choose m) of subsets of size m.  binom(L, m, pas) returns this
binomial coefficient.  The cells pas, …, pas + L hold a row of Pascal's triangle.  Row 0 is 1
followed by zeros (`binomFirst_spec`), and the next row is formed in place, from right to left, so
that the two entries that are added are still those of the old row.  `binomPlace_spec` treats one
entry, by Pascal's rule, `binomInner_spec` one row, and `binom_spec` runs through the rows;
`binom_entry` is the specification that the callers of the procedure assume.
-/


namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Binom

/- The local variables of binom: Levels = L, Size = m, Addr = pas (the arguments); Row is the
number of the row, and Place the place in it. -/
slots Levels Size Addr Row Place

end Binom

open Binom

/-- One entry of the next row: the entry above it plus the entry to the left of that. -/
def binomPlace : Stmt :=
  .store (v Addr +' v Place) (M (v Addr +' v Place) +' M (v Addr +' v Place -' k 1)) ;;
  .set Place (v Place -' k 1)

/-- The loop that turns row i of the triangle into row i + 1, from right to left. -/
def binomInner : Stmt := .while (k 0 <' v Place) binomPlace

/-- One round of the loop over the rows. -/
def binomRow : Stmt := .set Place (v Levels) ;; binomInner ;; .set Row (v Row +' k 1)

/-- Row 0 of the triangle: 1 followed by L zeros. -/
def binomFirst : Stmt :=
  .store (v Addr) (k 1) ;;
  .set Place (k 1) ;;
  .while (v Place <' v Levels +' k 1) (
    .store (v Addr +' v Place) (k 0) ;;
    .set Place (v Place +' k 1))

/-- binom(L, m, pas).  The number of the row is not set at the beginning: local variables that are
not arguments start at 0.  The result of a procedure is what it leaves in local variable 0. -/
def binomBody : Stmt :=
  binomFirst ;;
  .while (v Row <' v Levels) binomRow ;;
  .set Levels (M (v Addr +' v Size))

namespace Binom

/-! ## One row from the row before it -/

/-- The memory while row i is turned into row i + 1: the entries to the right of place p are those
of row i + 1, the others still those of row i; no cell outside the L + 2 cells that the procedure
may use has changed. -/
def Mixed (μ : ℕ → ℤ) (L pas i p : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ j ≤ L, μ' (pas + j) = if p < j then (((i + 1).choose j : ℕ) : ℤ) else (i.choose j : ℕ)) ∧
    SameOutside μ μ' pas (L + 2)

/-- One more entry has been replaced. -/
theorem Mixed.step {μ μ' : ℕ → ℤ} {L pas i p : ℕ} (h : Mixed μ L pas i (p + 1) μ')
    (hp : p + 1 ≤ L) :
    Mixed μ L pas i p (Function.update μ' (pas + (p + 1)) ((i + 1).choose (p + 1) : ℕ)) := by
  refine ⟨fun j hj => ?_, h.2.update ⟨by omega, by omega⟩ _⟩
  by_cases hjp : j = p + 1
  · simp_all
  · rw [Function.update_of_ne (by omega), h.1 j hj]
    omega

variable {μ : ℕ → ℤ} {L m pas i : ℕ} {T : ℕ} {Q : State → Prop}

/-- The state after r entries have been replaced: the place is L - r. -/
def Inv (μ : ℕ → ℤ) (L m pas i r : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [L, m, pas, i, (L - r : ℕ)], μ'⟩ ∧ Mixed μ L pas i (L - r) μ'

variable {σ : State}

/-- **One entry**, by Pascal's rule. -/
theorem binomPlace_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hi : i < L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) {r : ℕ} (hr : r < L)
    (h : Inv μ L m pas i r σ) :
    Ends lim P d binomPlace σ binomPlace.blockCost (Inv μ L m pas i (r + 1)) := by
  obtain ⟨μ', rfl, hI⟩ := h
  obtain ⟨p, hp⟩ : ∃ p, L - r = p + 1 := by simp_all
  unfold Inv
  rw [hp] at hI ⊢
  rw [show L - (r + 1) = p by omega]
  -- The two entries that are added are still those of row i, and their sum fits in a word.
  have habove : μ' (pas + (p + 1)) = i.choose (p + 1) := by
    rw [hI.1 _ (by omega), if_neg (by omega)]
  have hleft : μ' (pas + p) = i.choose p := by rw [hI.1 p (by omega), if_neg (by omega)]
  have hsum : (i + 1).choose (p + 1) = i.choose p + i.choose (p + 1) := by grind
  have hfits : (i + 1).choose (p + 1) ≤ 2 ^ L :=
    (Nat.choose_le_two_pow _ _).trans (by simp_all [Nat.pow_le_pow_right])
  have haddr : (pas + ((p : ℤ) + 1) - 1).toNat = pas + p := by omega
  have haddr' : (pas + ((p : ℤ) + 1)).toNat = pas + (p + 1) := by omega
  unfold binomPlace
  -- mem[pas + Place] := mem[pas + Place] + mem[pas + Place - 1]; Place := Place - 1
  light_store (pas + (p + 1)) ((i + 1).choose (p + 1)) using habove, hleft, haddr, haddr', hsum
  light_set p
  exact ⟨_, rfl, hI.step (by omega)⟩

/-- **One row**: the loop over the places turns row i of the triangle into row i + 1. -/
theorem binomInner_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hi : i < L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) (hrow : ∀ j ≤ L, μ (pas + j) = (i.choose j : ℕ))
    (done : ∀ μ' : ℕ → ℤ, (∀ j ≤ L, μ' (pas + j) = ((i + 1).choose j : ℕ)) →
      SameOutside μ μ' pas (L + 2) → Q ⟨frame [L, m, pas, i, 0], μ'⟩)
    (hT : 23 * L + 4 ≤ T) :
    Ends lim P d binomInner ⟨frame [L, m, pas, i, L], μ⟩ T Q := by
  refine Ends.whileConst (Inv μ L m pas i) L binomPlace.blockCost ?_ ?_ ?_
    (by simp [binomPlace]; omega)
  · exact ⟨μ, rfl, by simp_all, .refl⟩
  ·
    intro r σ hr h
    have hplace := binomPlace_spec (P := P) (d := d) std hsp hi hw hr h
    obtain ⟨μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hplace⟩
  ·
    rintro _ ⟨μ', rfl, hcells, same⟩
    refine ⟨by light_side, by light_side, ?_⟩
    simp_all

/-! ## The loop over the rows -/

/-- The state before round i: the cells hold row i of the triangle. -/
def RowAt (μ : ℕ → ℤ) (L m pas i : ℕ) (σ : State) : Prop :=
  ∃ (p : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [L, m, pas, i, p], μ'⟩ ∧
    (∀ j ≤ L, μ' (pas + j) = (i.choose j : ℕ)) ∧ SameOutside μ μ' pas (L + 2)

/-- The time of one round of the loop over the rows. -/
def tRow (L : ℕ) : ℕ := 23 * L + 10

/-- **One round of the loop over the rows** turns row `i` of the triangle into row `i + 1`. -/
theorem binomRow_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hi : i < L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) (h : RowAt μ L m pas i σ) :
    Ends lim P d binomRow σ (tRow L) (RowAt μ L m pas (i + 1)) := by
  obtain ⟨p, μ', rfl, hrow, same⟩ := h
  unfold binomRow tRow
  -- Place := L
  light_set L
  refine Ends.next _ (binomInner_spec std hsp hi hw hrow ?_ le_rfl)
  intro μ'' hnew same'
  -- Row := Row + 1
  light_set (i + 1)
  exact ⟨_, _, rfl, hnew, same.trans same'⟩

/-- **Row 0** of the triangle is written: 1 followed by `L` zeros. -/
theorem binomFirst_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space)
    (done : ∀ σ, RowAt μ L m pas 0 σ → Q σ) (hT : 15 * L + 11 ≤ T) :
    Ends lim P d binomFirst ⟨frame [L, m, pas], μ⟩ T Q := by
  light_store pas 1
  light_set (0 + 1)
  apply Ends.whileBlock
    (fun q σ => σ = ⟨frame [L, m, pas, 0, (q + 1)],
      wrote (Function.update μ pas 1) (pas + 1) (fun _ => 0) q⟩) L
  ·
    simp_all [wrote_zero]
  ·
    rintro q _ hq rfl
    have haddr : (pas + ((q : ℤ) + 1)).toNat = pas + 1 + q := by omega
    -- mem[pas + Place] := 0; Place := Place + 1
    exact ⟨by light_side, by light_side, by light_side,
      by simp_all [update_frame_setLocal, wrote_succ]⟩
  ·
    rintro _ rfl
    refine ⟨by light_side, by light_side, done _ ⟨_, _, rfl, fun j hj => ?_,
      (SameOutside.refl.update ⟨by omega, by omega⟩ 1).trans
        ((sameOutside_wrote le_rfl).mono (by omega) (by omega))⟩⟩
    -- (0 choose 0) = 1, and (0 choose j + 1) = 0.
    cases j with
    | zero => rw [wrote_rest, Nat.add_zero, Function.update_self]; rfl
    | succ j => rw [← Nat.add_assoc, Nat.add_right_comm, wrote_done]; rfl

end Binom

variable {μ : ℕ → ℤ} {L m pas : ℕ}

/-- **binom** returns (L choose m) and changes no cell outside the L + 2 cells from pas. -/
theorem binom_spec (std : Std lim) (hsp : pas + (L + 2) ≤ lim.space) (hm : m ≤ L)
    (hw : ((2 ^ L : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d binomBody ⟨frame [L, m, pas], μ⟩ (30 * (L + 1) ^ 2) fun σ' =>
      σ'.loc 0 = (L.choose m : ℕ) ∧ SameOutside μ σ'.mem pas (L + 2) := by
  refine Ends.next _ (binomFirst_spec std hsp ?_ le_rfl) (by ring_nf; omega)
  intro σ hfirst
  -- while Row < L; the L rounds take L (23 L + 14) steps
  refine Ends.next _ (Ends.whileConst (RowAt μ L m pas) L (tRow L) hfirst ?_ ?_ le_rfl)
    (by simp [tRow]; grind)
  ·
    intro i σ hi h
    have hrow := binomRow_spec (P := P) (d := d) std hsp hi hw h
    obtain ⟨p, μ', rfl, -⟩ := h
    simp_all
  ·
    rintro _ ⟨p, μ', rfl, hrow, same⟩
    refine ⟨by light_side, by light_side, ?_⟩
    -- The result: local 0 := mem[pas + m]
    exact Ends.setTo (L.choose m) ⟨by simp, same⟩
      (by light_side [hrow m hm]) (by simp [tRow]; grind)

/-- **The specification that the callers of binom assume.** -/
theorem binom_entry (std : Std lim) (hP : P[pBinom]? = some binomBody) {c : ℕ} (hc : 30 ≤ c := by decide) :
    BinomSpec lim P c :=
  fun _ _ _ _ hsp hm hw _ _ => .mono_const (.of_body hP (binom_spec std hsp hm hw)) hc
