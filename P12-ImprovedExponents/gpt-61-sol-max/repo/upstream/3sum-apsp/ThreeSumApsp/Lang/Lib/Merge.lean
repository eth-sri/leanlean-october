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
# Merging two segments

merge(a, na, b, nb, dst) writes the merge of the na cells from a and the nb cells from b to the na +
nb cells from dst, within `mergeTime (na + nb)` steps (`merge_meets`).  The model is `List.merge`:
the next output is the head of the first list unless the head of the second list is smaller.
Nothing is assumed about the order of the two lists.  Numbers are only compared and copied, so their
size does not matter.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Merge

/-! ## The pure side: one step of List.merge on the rests of two lists -/

variable {l r : List ℤ} {i j : ℕ}

theorem step_left hi (hj : j < r.length) (h : l[i] ≤ r[j]) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  grind [List.drop_eq_getElem_cons, List.cons_merge_cons]

theorem step_right hi hj (h : r[j] < l[i]) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  grind [List.drop_eq_getElem_cons, List.cons_merge_cons]

theorem step_left_end hi (hj : r.length ≤ j) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  grind [List.drop_eq_nil_of_le, List.merge_right, List.drop_eq_getElem_cons]

theorem step_right_end (hi : l.length ≤ i) hj :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  grind [List.drop_eq_nil_of_le, List.nil_merge, List.drop_eq_getElem_cons]

end Merge

/-! ## The program -/



/-- The next output is the head of the first list: dst[i + j] := a[i]; i := i + 1. -/
def mergeTakeLeft  :=
  .store (v 4 +' v 5 +' v 6) (M (v 0 +' v 5)) ;;
  .set 5 (v 5 +' k 1)


/-- The next output is the head of the second list: dst[i + j] := b[j]; j := j + 1. -/
def mergeTakeRight  :=
  .store (v 4 +' v 5 +' v 6) (M (v 2 +' v 6)) ;;
  .set 6 (v 6 +' k 1)


/-- merge(a, na, b, nb, dst). -/
def mergeBody  :=
  .set 5 (k 0) ;;
  .set 6 (k 0) ;;
  .while (v 5 +' v 6 <' v 1 +' v 3) (
    .ite (v 5 <' v 1)
      (.ite (v 6 <' v 3)
        (.ite (M (v 2 +' v 6) <' M (v 0 +' v 5)) mergeTakeRight mergeTakeLeft)
        mergeTakeLeft)
      mergeTakeRight)

namespace Merge

/-- What merge assumes: the two lists lie in the memory, and the output region is within the memory
and meets neither of them. -/
structure Pre (lim : Limits) (μ : Light.Memory) (a b dst : ℕ) (l r : List ℤ) : Prop where
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
def Inv μ (a b dst : ℕ) (l r : List ℤ) (i j : ℕ) (σ : State) :=
  ∃ (μ' : Light.Memory) (out : List ℤ), σ = ⟨frame [a, l.length, b, r.length, dst, i, j], μ'⟩ ∧
    i ≤ l.length ∧ j ≤ r.length ∧ SameOutside μ μ' dst (l.length + r.length) ∧
    out.length = i + j ∧ Seg μ' dst out ∧ out ++ (l.drop i).merge (r.drop j) = l.merge r

/-- The invariant of the loop: t cells have been taken. -/
def Taken μ a b dst l r t σ :=
  ∃ i j, i + j = t ∧ Inv μ a b dst l r i j σ

variable {μ : Light.Memory} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}

variable (C : Pre lim μ a b dst l r)

include C in
/-- dst[i + j] := a[i]; i := i + 1. -/
theorem takeLeft  {σ} (h : Inv μ a b dst l r i j σ)
     hi
    (hm : (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j)) :
    mergeTakeLeft.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, -, hj, same, hlen, seg, hout⟩ := h
  light_facts C


  refine ⟨by light_side [mergeTakeLeft], i + 1, j, by omega,
    Function.update μ' (dst + out.length) l[i], out ++ [l[i]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by light_side,
    seg.snoc _, by rw [← hout, hm]; simp⟩
  simp [mergeTakeLeft, update_frame_setLocal, (by omega : ((dst : ℤ) + i + j).toNat = dst + out.length), (same _ (by omega)).trans (C.segL.get hi)]

include C in
/-- dst[i + j] := b[j]; j := j + 1. -/
theorem takeRight  {σ} (h : Inv μ a b dst l r i j σ)
     hj
    (hm : (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1))) :
    mergeTakeRight.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, hi, -, same, hlen, seg, hout⟩ := h
  light_facts C


  refine ⟨by light_side [mergeTakeRight], i, j + 1, rfl,
    Function.update μ' (dst + out.length) r[j], out ++ [r[j]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by light_side,
    seg.snoc _, by rw [← hout, hm]; simp⟩
  simp [mergeTakeRight, update_frame_setLocal, (by omega : ((dst : ℤ) + i + j).toNat = dst + out.length), (same _ (by omega)).trans (C.segR.get hj)]

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
  unfold mergeTime
  -- i := 0; j := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while i + j < na + nb
  refine Ends.whileBlock (Taken μ a b dst l r) (l.length + r.length) ?start ?round ?done
    (by ram_safe [mergeTakeLeft, mergeTakeRight])
  case start =>
    exact ⟨0, 0, rfl, μ, [], rfl, Nat.zero_le _, Nat.zero_le _, .refl, rfl, Seg.nil, rfl⟩
  case done =>
    rintro _ ⟨i, j, hij, μ', out, rfl, hi, hj, same, hlen, seg, hout⟩
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)] at hout
    exact ⟨by light_side, by simp; omega, by simpa [← hout] using seg, same⟩
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
      · have  := (same _ (by omega)).trans (C.segL.get c1)
        have  := (same _ (by omega)).trans (C.segR.get c2)
        refine .ite_pos ?_
        by_cases c3 : r[j] < l[i]
        · exact .ite_pos (right c2 (step_right c1 c2 c3)) (by simp_all)
        · exact .ite_neg (left c1 (step_left c1 c2 (not_lt.1 c3)))
            (by simp_all)
      · exact .ite_neg (left c1 (step_left_end c1 (by omega)))
    · exact .ite_neg (right (by omega) (step_right_end (by omega) (by omega)))

end Merge

end Light
