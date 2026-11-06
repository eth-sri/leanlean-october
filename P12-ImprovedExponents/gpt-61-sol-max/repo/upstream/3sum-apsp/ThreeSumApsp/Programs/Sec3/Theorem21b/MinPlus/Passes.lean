/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Lang.Calls
public import ThreeSumApsp.Lang.Lib.Pass

/-!
# Two passes over an array, for the (min,+)-product found bit by bit

Two routines of the host for [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).

addc(len, x, src, dst): dst[i] := src[i] + x, in at most 19 len + 6 steps (addc_meets).
bump(len, x, fl, lo): lo[i] := lo[i] + x (1 − fl[i]), in at most 30 len + 6 steps: where the flag
is 0 the entry grows by x (bump_meets).
Both change no other cell.  Each is one pass, so each proof only says what round j reads.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}


/-- addc(len, x, src, dst): for i < len, dst[i] := src[i] + x. -/
def addcBody  := pass 4 (v 0) (v 3) (M (v 2 +' v 4) +' v 1)

/-- bump(len, x, fl, lo): for i < len, lo[i] := lo[i] + x (1 − fl[i]). -/
def bumpBody  :=
  pass 4 (v 0) (v 3)
    (M (v 3 +' v 4) +' v 1 *' (k 1 -' M (v 2 +' v 4)))

/-- **addc** writes the list with x added to every entry to dst and changes nothing else. -/
theorem addc_meets {p} (hp : P[p]? = some addcBody) {μ} {src len} {L}
     x dst (hL : Seg μ src L) (hlen : L.length = len)
    (hsep : Apart src len dst len)
    (hlim : lim.space ≤ lim.word ∧ src + len ≤ lim.space ∧ dst + len ≤ lim.space)
    (hfits : ∀ y ∈ L, |y + x| ≤ lim.word) :
    Meets lim P p d [len, x, src, dst] μ (19 * len + 6) fun _ μ' =>
      Seg μ' dst (L.map (· + x)) ∧ SameOutside μ μ' dst len := by
  subst hlen
  obtain ⟨hw, hsrc, hdst⟩ := hlim
  set f : Light.Memory := fun i => L.getD i 0 + x with hf

  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hw hdst rfl rfl)
  · -- round j reads src[j], which lies outside the cells that are written
    have  : wrote μ dst f j (src + j) = L[j] := (wrote_rest (by omega)).trans (hL j hj)
    simp_all [Limits.Addr, abs_le] <;> omega
  · dsimp only
    refine ⟨fun i hi => ?_, sameOutside_wrote le_rfl⟩
    grind [wrote_done]

/-- **bump** adds x (1 − flag) to every entry of the list at lo and changes nothing else.  The flags
are 0 or 1, and V bounds the entries. -/
theorem bump_meets {p} (hp : P[p]? = some bumpBody) {μ} {fl lo len} {F L}
    {V} x (hF : Seg μ fl F) (hL : Seg μ lo L) (hlen : F.length = len ∧ L.length = len)
    (hsep : Apart fl len lo len)
    (hlim : lim.space ≤ lim.word ∧ fl + len ≤ lim.space ∧ lo + len ≤ lim.space)
    (hflag : ∀ f ∈ F, f = 0 ∨ f = 1) (hle : AbsLe L V) (hfits : |x| + V ≤ lim.word ∧ 1 ≤ lim.word) :
    Meets lim P p d [len, x, fl, lo] μ (30 * len + 6) fun _ μ' =>
      Seg μ' lo (List.zipWith (fun l f => l + x * (1 - f)) L F) ∧ SameOutside μ μ' lo len := by

  obtain ⟨hw, hfl, hlo⟩ := hlim
  set f : Light.Memory := fun i => L.getD i 0 + x * (1 - F.getD i 0) with hf

  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hw hlo rfl rfl)
  · -- round j reads the flag fl[j], which is never written, and lo[j], which it then overwrites
    have  : wrote μ lo f j (fl + j) = F[j] := (wrote_rest (by omega)).trans (hF j (by omega))
    have  : wrote μ lo f j (lo + j) = L[j] := (wrote_rest (by omega)).trans (hL j (by omega))
    have  := abs_le.1 (hle.getElem (i := j) (by omega))
    have  := abs_le.1 (le_refl |x|)
    rw [update_frame_setLocal]
    rcases hflag _ (List.getElem_mem (show j < F.length by omega)) with h | h
    all_goals
      simp_all [Limits.Addr, abs_le] <;> omega
  · grind [seg_wrote, sameOutside_wrote]

end Light.Sec3
