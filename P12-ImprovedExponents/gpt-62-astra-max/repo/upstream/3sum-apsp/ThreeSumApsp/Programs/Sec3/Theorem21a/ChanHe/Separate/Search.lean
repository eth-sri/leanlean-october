/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Separate.Job

@[expose] public section
namespace Light.Sec3.ChanHe.Separate
open ThreeSumApsp

open Param in
/-- Four nested bounded existential searches use the same short procedure at
four link addresses. The fresh coordinate is shifted into the last slot. -/
def anyBody (next : ℕ) : Stmt :=
  .set 19 (k 0) ;; .for 17 (v Bound) (
    .call next ([v Bound,v GapB,v GapC,v GapD,v 17] ++ tail) 18 ;;
    .ite (v 18 =' k 1) (.set 19 (k 1)) .skip) ;; .set 0 (v 19)

def Probe (lim : Limits) (P : Program) (p : ℕ) (w : Job) (flight time : ℕ) (R : (ℕ → ℤ) → Prop)
    (F : ℕ → ℕ → ℕ → ℕ → Prop) := ∀ a < w.B, ∀ b < w.B, ∀ c < w.B, ∀ e < w.B, ∀ μ, R μ → ∀ d,
    d+flight ≤ lim.depth → Meets lim P p d (w.args a b c e) μ time fun z ν => z = flag (F a b c e) ∧ R ν

private abbrev searchState (w : Job) (a b c e j : ℕ) (s : ℤ × ℤ) (ν : ℕ → ℤ) : State :=
  ⟨frame (w.args a b c e ++ [(j:ℤ),s.1,s.2]),ν⟩

set_option maxHeartbeats 850000 in
theorem probe_any {lim : Limits} {P : Program} {next p flight time R F} {w : Job}
    (hp : P[p]? = some (anyBody next)) (k : Probe lim P next w flight time R F)
    (hB : (w.B:ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word) :
    Probe lim P p w (flight+1) (moreTime w.B time) R (fun _ b c e => ∃ i<w.B, F b c e i) := by
  intro a ha b hb c hc e he μ hμ d hd
  apply Meets.of_body hp
  unfold anyBody moreTime
  let seen (j : ℕ) := ∃ i<j,F b c e i
  have zero : flag (seen 0) = 0 := flag_of_not (by simp [seen])
  have step (j : ℕ) : seen (j+1) ↔ seen j ∨ F b c e j := Nat.exists_lt_succ_right
  have room : w.B*(time+70)+12 ≤ (w.B+1)*(time+80) := by simp [Nat.add_mul,Nat.mul_add]; omega
  light_set 0
  refine Ends.next (w.B*(time+70)+6) (Ends.forCarry (searchState w a b c e)
    (fun j s ν => s.2 = flag (seen j) ∧ R ν) w.B (time+60) (0,0) ⟨zero.symm,hμ⟩ ?_ ?_
    (hT := by simp; nlinarith)) (by light_time)
  · rintro j ⟨_,z⟩ ν hj ⟨rfl,hν⟩
    unfold searchState Job.args Job.tail
    light_call (k b hb c hc e he j hj ν hν) with _ ν' ⟨rfl,hr⟩
    by_cases h : F b c e j
    · rw [flag_of h]
      light_if yes no : True
      · light_set 1
        exact ⟨(1,1),ν',rfl,(flag_of ((step j).2 (.inr h))).symm,hr⟩
      · contradiction
    · rw [flag_of_not h]
      light_if yes no : False
      · contradiction
      · exact Ends.skip ⟨(0,_),ν',rfl,(flag_congr ((step j).trans (or_iff_left h))).symm,hr⟩
  · rintro ⟨_,z⟩ ν ⟨rfl,hr⟩
    unfold searchState Job.args Job.tail
    light_set (flag (seen w.B))
    exact ⟨rfl,hr⟩
end Light.Sec3.ChanHe.Separate
