/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# Looking up a string in a trie (Section 4.3)

"looking up or inserting a box, takes O(L) operations": the routine follows the symbols of the box
down from the root.  A vertex is a block of eleven consecutive cells of the trie area, one for each
symbol, holding the address of the child; a vertex at depth L holds the value in its first cell.
Addresses are relative to the base of the area, so the model is `Spec.trieLookup` on the array T
that the area holds.

The loop goes down one level in each round.  Its invariant (`Lookup.Inv`) says that the walk from
the current vertex along the rest of the string ends where the walk from the root along the whole
string ends, and that it stays inside the array (`Spec.WalkOK`); `Lookup.walk_step` says what one
step down does to both facts.  `lookup_spec` is the specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp.Spec


/-- lookup(area, root, key, len): follow the symbols of the string down from the root, and return
the first cell of the vertex that is reached. -/
def lookupBody  :=
  .set 4 (k 0) ;;
  .while (v 4 <' v 3) (
    .set 1 (M (v 0 +' v 1 +' M (v 2 +' v 4))) ;;
    .set 4 (v 4 +' k 1)) ;;
  .set 0 (M (v 0 +' v 1))

namespace Lookup

variable {T : List ℤ} {kl : List ℕ} {p i : ℕ}

/-- One step down: the current vertex lies inside the array, the pointer for the next symbol is
positive, and the walk goes on from the child. -/
private theorem walk_step hi (hok : WalkOK T p (kl.drop i)) :
    p + 11 ≤ T.length ∧ 0 < T.getD (p + kl[i]) 0 ∧
      WalkOK T (T.getD (p + kl[i]) 0).toNat (kl.drop (i + 1)) ∧
      trieWalk T p (kl.drop i) = trieWalk T (T.getD (p + kl[i]) 0).toNat (kl.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi] at hok ⊢
  exact ⟨hok.2.1, hok.2.2.1, hok.2.2.2, rfl⟩

/-- Before round i: the walk from the current vertex p along the rest of the string stays inside the
array and ends where the walk from the root ends.  The memory is not changed. -/
def Inv (tr root key : ℕ) T kl μ (i : ℕ) (σ : State) :=
  ∃ p : ℕ, σ = ⟨frame [tr, p, key, kl.length, i], μ⟩ ∧ WalkOK T p (kl.drop i) ∧
    trieWalk T root kl = trieWalk T p (kl.drop i)

end Lookup

open Lookup in
/-- **lookup** returns the value stored for the string, and leaves the memory as it was. -/
theorem lookup_spec {lim } {P } (hP : P[45]? = some lookupBody)
    (hs : Std lim) : LookupSpec lim P := by
  rintro tr root key _ T kl μ hT hkey rfl hd hwalk htr hkeyB
  refine fun d _ => ⟨lookupBody, hP, ?_⟩
  light_facts hs
  unfold tLookup
  -- level := 0
  light_set (0 : ℕ)
  -- while level < len
  refine Ends.next _ (Ends.whileBlock (Inv tr root key T kl μ) kl.length ?start ?round ?done
    (hT := le_rfl))
  case start => exact ⟨root, rfl, hwalk, rfl⟩
  case round =>
    rintro i _ hi ⟨p, rfl, hok, hwk⟩
    obtain ⟨hpT, hpos, hok', hstep⟩ := walk_step hi hok
    have  := hd _ (List.getElem_mem hi)
    have hcell := hkey.getElem hi

    have haddr : ((tr : ℤ) + p + kl[i]).toNat = tr + (p + kl[i]) := by omega
    -- vertex := mem[area + vertex + mem[key + level]]; level := level + 1
    refine ⟨by light_side, by light_side, by light_side [hcell],
      (T.getD (p + kl[i]) 0).toNat, ?_, hok', hwk.trans hstep⟩
    rw [Int.toNat_of_nonneg hpos.le]
    simp [update_frame_setLocal, hcell, haddr, (hT.getD (by omega) 0 : μ (tr + (p + kl[i])) = T.getD (p + kl[i]) 0)]
  case done =>
    rintro _ ⟨p, rfl, hok, hwk⟩
    rw [List.drop_of_length_le le_rfl] at hok hwk
    have  := hok.2

    refine ⟨by light_side, by light_side, ?_⟩
    -- return mem[area + vertex]
    light_set (T.getD p 0) using (hT.getD (by omega) 0 : μ (tr + p) = T.getD p 0)
    refine ⟨?_, rfl⟩
    rw [trieLookup, hwk]
    rfl

end Light.Sec4
