/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Slots

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

namespace Pass

/-- The local variables of addc and bump: the arguments len, x (Summand), the array that is only
read (src or fl) and the array that is written (dst or lo), and the counter. -/
slots 0 Len Summand Source Dest Index

end Pass

open Pass in
/-- bump(len, x, fl, lo): for i < len, lo[i] := lo[i] + x (1 − fl[i]). -/
def bumpBody : Stmt :=
  pass Index (v Len) (v Dest)
    (M (v Dest +' v Index) +' v Summand *' (k 1 -' M (v Source +' v Index)))

/-- **bump** adds x (1 − flag) to every entry of the list at lo and changes nothing else.  The flags
are 0 or 1, and V bounds the entries. -/
theorem bump_meets {p } (hp : P[p]? = some bumpBody) {μ } {fl lo len } {F L }
    {V } (x : ℤ) (hF : Seg μ fl F) (hL : Seg μ lo L) (hlen : F.length = len ∧ L.length = len)
    (hsep : Apart fl len lo len)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ fl + len ≤ lim.space ∧ lo + len ≤ lim.space)
    (hflag : ∀ f ∈ F, f = 0 ∨ f = 1) (hle : AbsLe L V) (hfits : |x| + V ≤ lim.word ∧ 1 ≤ lim.word) :
    Meets lim P p d [(len : ℤ), x, fl, lo] μ (30 * len + 6) fun _ μ' =>
      Seg μ' lo (List.zipWith (fun l f => l + x * (1 - f)) L F) ∧ SameOutside μ μ' lo len := by
  obtain ⟨lF, lL⟩ := hlen
  obtain ⟨hw, hfl, hlo⟩ := hlim
  set f : ℕ → ℤ := fun i => L.getD i 0 + x * (1 - F.getD i 0) with hf
  have hfi : ∀ i (hF : i < F.length) (hL : i < L.length), f i = L[i] + x * (1 - F[i]) :=
    by grind
  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hw hlo rfl rfl)
  · -- round j reads the flag fl[j], which is never written, and lo[j], which it then overwrites
    have hreadF : wrote μ lo f j (fl + j) = F[j] := (wrote_rest (by omega)).trans (hF j (by omega))
    have hreadL : wrote μ lo f j (lo + j) = L[j] := (wrote_rest (by omega)).trans (hL j (by omega))
    have hentry := abs_le.1 (hle.getElem (i := j) (by omega))
    have hx := abs_le.1 (le_refl |x|)
    rcases hflag _ (List.getElem_mem (show j < F.length by omega)) with h | h
    all_goals
      simp [Limits.Addr, abs_le, hreadF, hfi j (by omega) (by omega), h]; omega
  · exact ⟨by apply seg_wrote <;> grind, sameOutside_wrote le_rfl⟩

end Light.Sec3
