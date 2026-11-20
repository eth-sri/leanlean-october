/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.Lib.Filter
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
public import ThreeSumApsp.Spec.Sec3.Theorem21a.Passes

/-! A single pass extracts the distinct values from an already sorted array. -/

@[expose] public section



namespace Light.Sec3.ChanHe

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Distinct
registers [Len, Src, Val, Idx, Values]

def takeValue : Expr := M (v Src +' v Idx)
def test : Guard :=
  .either (.atom (v Values =' k 0))
    (.neg (.atom (takeValue =' M (v Val +' v Values -' k 1))))
end Distinct

open Distinct in
def distinctBody : Stmt := filterPass Idx Len Val Values test takeValue ;; .set Len (v Values)

open Distinct in
theorem distinct_spec {p : ℕ} (hP : P[p]? = some distinctBody) : DistinctSpec lim P p := by
  intro d a val L μ C
  light_facts C
  refine Meets.of_body hP ?_
  unfold distinctBody
  refine Ends.next _ (Ends.filterPass _ _ (fun i D => DistSt L D i) (DistSt.zero L) ?_ ?_
    C.space_le C.spaceVal rfl rfl (hT := le_rfl)) (by light_time [filterStep, test, takeValue, tDistinct])
  · intro i D ν hi hD H
    have hle := H.size
    have h := (H.same (a + i) (by omega)).trans (C.seg.getD hi 0)
    have hm (hn : D.length ≠ 0) : ((val : ℤ) + D.length - 1).toNat = val + (D.length - 1) := by omega
    have hv (hn : D.length ≠ 0) : ν (val + (D.length - 1)) = D.getD (D.length - 1) 0 :=
      H.seg.getD (by omega) 0
    refine ⟨by by_cases hz : D.length = 0 <;> light_side [test, takeValue, hz], by light_side [takeValue], ?_, ?_⟩
    · intro hs
      have he : D.length = 0 ∨ L.getD i 0 ≠ D.getD (D.length - 1) 0 := by
        by_cases hn : D.length = 0
        · exact .inl hn
        · simpa [test, takeValue, h, hn, hm hn, hv hn] using hs
      simpa [takeValue, h] using hD.opens C.sorted hi he
    · intro hs
      have hn : D.length ≠ 0 := fun he => hs (.inl (by simpa using he))
      exact hD.bumps hi (by omega) (by simpa [test, takeValue, h, hn, hm hn, hv hn] using hs)
  · intro D ν hD H
    refine Ends.setLast ⟨⟨D, rfl, hD.nodup, ?_, H.seg⟩, H.same.mono le_rfl (Nat.add_le_add_left H.size _)⟩
      (hT := by light_time [filterStep, test, takeValue, tDistinct])
    ext z
    simpa using hD.mem z

end Light.Sec3.ChanHe
