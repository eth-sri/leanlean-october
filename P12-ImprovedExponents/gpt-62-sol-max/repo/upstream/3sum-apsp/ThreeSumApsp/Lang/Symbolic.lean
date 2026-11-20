/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics

public section

namespace Light

macro "light_value" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| ((try simp [$hs,*]) <;> rfl))

/-- Advance a framed assignment or store, using evaluation and simplification to find
its value. Unlike `light_set` and `light_store`, no symbolic result is supplied. -/
macro "light_step" " using " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    focus
      light_head
      first
      | (refine Ends.setToThen ?_ ?_ ⟨?_, ?_⟩ ?_
         on_goal -1 => light_time [$hs,*]
         on_goal -1 => light_value [$hs,*]
         on_goal -1 => (first | assumption | omega | light_side [$hs,*]))
      | (refine Ends.storeToThen ?_ ?_ ?_ ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ ?_
         on_goal -1 => light_time [$hs,*]
         on_goal -4 =>
           ((try simp [$hs,*]) <;> (try simp only [← Int.natCast_add, ← Int.natCast_mul]) <;> rfl)
         on_goal -2 => light_value [$hs,*]
         on_goal -1 => (first | assumption | omega | light_side [$hs,*])
         on_goal -1 => (first | assumption | omega | light_side [$hs,*])
         on_goal -1 => (first | assumption | omega | light_side [$hs,*]))
      try light_skip)

macro "light_step" : tactic => `(tactic| light_step using)

macro "light_steps" " using " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (light_step using $hs,*; repeat light_step using $hs,*))

macro "light_steps" : tactic => `(tactic| light_steps using)
/-- Verify a loop- and call-free block by normalizing its safety and final state. -/
macro "light_block" " using " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    focus
      first
      | (refine Ends.block ?_ ?_
         on_goal -1 => light_time [$hs,*])
      | skip
      refine And.intro ?_ ?_
      on_goal -2 => (first | trivial | light_side [$hs,*])
      first
      | rfl
      | (simp [update_frame_setLocal, $hs,*]
         try ring_nf))

macro "light_block" : tactic => `(tactic| light_block using)

end Light
