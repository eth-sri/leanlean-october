/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Seg
import ThreeSumApsp.Lang.Tactics

/-!
# Merging two segments

merge(a, na, b, nb, dst) writes the merge of the na cells from a and the nb cells from b to the na +
nb cells from dst, within `mergeTime (na + nb)` steps (`merge_meets`).  The model is `List.merge`:
the next output is the head of the first list unless the head of the second list is smaller.
Nothing is assumed about the order of the two lists.  Numbers are only compared and copied, so their
size does not matter.
-/


namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Merge

/-! ## The pure side: one step of List.merge on the rests of two lists -/

variable {l r : List ℤ} {i j : ℕ}

theorem step_left (hi : i < l.length) (hj : j < r.length) (h : l[i] ≤ r[j]) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  grind [List.drop_eq_getElem_cons, List.cons_merge_cons]

theorem step_right (hi : i < l.length) (hj : j < r.length) (h : r[j] < l[i]) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  grind [List.drop_eq_getElem_cons, List.cons_merge_cons]

theorem step_left_end (hi : i < l.length) (hj : r.length ≤ j := by omega) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  grind [List.drop_eq_nil_of_le, List.merge_right, List.drop_eq_getElem_cons]

theorem step_right_end (hi : l.length ≤ i) (hj : j < r.length := by omega) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  grind [List.drop_eq_nil_of_le, List.nil_merge, List.drop_eq_getElem_cons]

end Merge

/-! ## The program -/

namespace Merge

/- The local variables of merge: the arguments a, na, b, nb, dst, and the numbers i and j of cells
already taken from the first and the second list. -/
slots ListA LenA ListB LenB Dest DoneA DoneB

end Merge

open Merge in
/-- The next output is the head of the first list: dst[i + j] := a[i]; i := i + 1. -/
def mergeTakeLeft : Stmt :=
  .store (v Dest +' v DoneA +' v DoneB) (M (v ListA +' v DoneA)) ;;
  .set DoneA (v DoneA +' k 1)

open Merge in
/-- The next output is the head of the second list: dst[i + j] := b[j]; j := j + 1. -/
def mergeTakeRight : Stmt :=
  .store (v Dest +' v DoneA +' v DoneB) (M (v ListB +' v DoneB)) ;;
  .set DoneB (v DoneB +' k 1)

open Merge in
/-- merge(a, na, b, nb, dst). -/
def mergeBody : Stmt :=
  .set DoneA (k 0) ;;
  .set DoneB (k 0) ;;
  .while (v DoneA +' v DoneB <' v LenA +' v LenB) (
    .ite (v DoneA <' v LenA)
      (.ite (v DoneB <' v LenB)
        (.ite (M (v ListB +' v DoneB) <' M (v ListA +' v DoneA)) mergeTakeRight mergeTakeLeft)
        mergeTakeLeft)
      mergeTakeRight)

namespace Merge

/-- What merge assumes: the two lists lie in the memory, and the output region is within the memory
and meets neither of them. -/
structure Pre (lim : Limits) (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  segL : Seg μ a l
  segR : Seg μ b r
  spaceL : a + l.length ≤ lim.space
  spaceR : b + r.length ≤ lim.space
  spaceD : dst + (l.length + r.length) ≤ lim.space
  sepL : Apart a l.length dst (l.length + r.length)
  sepR : Apart b r.length dst (l.length + r.length)

/-- The state after i cells of the first list and j cells of the second have been taken: they stand,
merged, in the first i + j cells of dst, and no cell outside dst has changed. -/
def Inv (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (i j : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (out : List ℤ), σ = ⟨frame [a, l.length, b, r.length, dst, i, j], μ'⟩ ∧
    i ≤ l.length ∧ j ≤ r.length ∧ SameOutside μ μ' dst (l.length + r.length) ∧
    out.length = i + j ∧ Seg μ' dst out ∧ out ++ (l.drop i).merge (r.drop j) = l.merge r

/-- The invariant of the loop: t cells have been taken. -/
def Taken (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ i j, i + j = t ∧ Inv μ a b dst l r i j σ

variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}

variable {σ : State}

/-- dst[i + j] := a[i]; i := i + 1. -/
theorem takeLeft (C : Pre lim μ a b dst l r) (h : Inv μ a b dst l r i j σ)
    (hi : i < l.length)
    (hm : (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j)) :
    mergeTakeLeft.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, -, hj, same, hlen, seg, hout⟩ := h
  light_facts C
  have hread := (same _ (by omega)).trans (C.segL.get hi)
  have haddr : ((dst : ℤ) + i + j).toNat = dst + out.length := by omega
  refine ⟨by light_side [mergeTakeLeft], i + 1, j, by omega,
    Function.update μ' _ _, out ++ [l[i]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by grind,
    seg.snoc _, by simp_all⟩
  simp_all [mergeTakeLeft, update_frame_setLocal]

/-- dst[i + j] := b[j]; j := j + 1. -/
theorem takeRight (C : Pre lim μ a b dst l r) (h : Inv μ a b dst l r i j σ)
    (hj : j < r.length)
    (hm : (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1))) :
    mergeTakeRight.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, hi, -, same, hlen, seg, hout⟩ := h
  light_facts C
  have hread := (same _ (by omega)).trans (C.segR.get hj)
  have haddr : ((dst : ℤ) + i + j).toNat = dst + out.length := by omega
  refine ⟨by light_side [mergeTakeRight], i, j + 1, by omega,
    Function.update μ' _ _, out ++ [r[j]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by grind,
    seg.snoc _, by simp_all⟩
  simp_all [mergeTakeRight, update_frame_setLocal]

/-- The time of merge, for n = na + nb numbers. -/
@[simp] def _root_.Light.mergeTime (n : ℕ) : ℕ := 40 * n + 12

/-- **merge(a, na, b, nb, dst)** writes `List.merge` of the two lists to dst and changes nothing
else. -/
theorem _root_.Light.merge_meets {p : ℕ} (hp : P[p]? = some mergeBody)
    (C : Pre lim μ a b dst l r) :
    Meets lim P p d [a, l.length, b, r.length, dst] μ (mergeTime (l.length + r.length)) fun _ μ' =>
      Seg μ' dst (l.merge r) ∧ SameOutside μ μ' dst (l.length + r.length) := by
  light_facts C
  refine .of_body hp ?_
  light_set 0
  light_set 0
  -- while i + j < na + nb
  refine Ends.whileBlock (Taken μ a b dst l r) (l.length + r.length) ?start ?round ?done
    (by simp [mergeTakeLeft, mergeTakeRight]; omega)
  case start =>
    exact ⟨0, 0, rfl, μ, [], rfl, Nat.zero_le _, Nat.zero_le _, .refl, rfl, Seg.nil, by simp⟩
  case done =>
    rintro _ ⟨i, j, hij, μ', out, rfl, hi, hj, same, hlen, seg, hout⟩
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)] at hout
    exact ⟨by light_side, by simp; omega, by simp_all, same⟩
  case round =>
    rintro _ σ ht ⟨i, j, rfl, hI⟩
    have left := takeLeft C hI
    have right := takeRight C hI
    obtain ⟨μ', out, rfl, hi, hj, same, -⟩ := hI
    refine ⟨by light_side, by simp; omega, ?_⟩
    -- The next output is the head of the first list unless the head of the second list is smaller.
    by_cases c1 : i < l.length
    · refine .ite_pos ?_
      by_cases c2 : j < r.length
      · have hreadL := (same _ (by omega)).trans (C.segL.get c1)
        have hreadR := (same _ (by omega)).trans (C.segR.get c2)
        refine .ite_pos ?_
        by_cases c3 : r[j] < l[i]
        · exact .ite_pos (by grind [step_right]) (by simp_all)
        · exact .ite_neg (by grind [step_left, not_lt])
            (by simp_all)
      · exact .ite_neg (by grind [step_left_end])
    · exact .ite_neg (by grind [step_right_end])
