/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ImprovedExponents.PrunedProgram.Boxes.Fill

@[expose] public section
namespace Light.Sec4.BoxTable
open ThreeSumApsp ThreeSumApsp.Spec

namespace Tile
slots 0 EncA EncB Page Cur Box Levels Mt E Ret

def body : Stmt := .while (v E ≤' v Mt) (
  .call Proc.fillList [v E,v EncA,v EncB,v Page,v Cur,v Box,v Levels,v Mt] Ret ;;
  .set E (v E +' k 1))

abbrev args (x : Tile) : List ℤ := [x.a,x.b,x.page,x.cur,x.box,x.L,(x.m-x.t:ℕ)]

abbrev Complete (x : Tile) (μ : ℕ → ℤ) := x.Done μ (x.m-x.t+1) 0

/-- Only the strings enumerating boxes and the current page are changed. -/
theorem spec {lim P d} (K : Passes lim P) (text : P[Proc.fillList]? = some Fill.body)
    {x : Tile} (H : x.Safe lim) {μ} (sa : SegOn x.m μ x.a x.A) (sb : SegOn x.m μ x.b x.B)
    (hd : d+3 ≤ lim.depth) : Ends lim P d body ⟨frame (args x),μ⟩ (tTile x.L x.m x.t)
      fun σ => x.Complete σ.mem ∧ Fill.kept x μ σ.mem := by
  let I (e : ℕ) (σ : State) := ∃ (r : ℤ) (ν : ℕ → ℤ), σ = ⟨frame (args x ++ [(e:ℤ),r]),ν⟩ ∧ x.Done ν e 0 ∧ Fill.kept x μ ν
  have hp := H.layout; have sizes := H.sizes; light_facts H.std
  refine (Ends.while I (x.m-x.t+1) (fun e => tFillList x.L (x.keys e).length + 30)
    ?start ?round ?done).mono ?time fun _ h => h
  case start => exact ⟨0,μ,congrArg (State.mk · μ) (frame_append_zeros _ 2).symm,
    fun _ _ _ h => by simp at h,SameOn.refl⟩
  case round =>
    rintro e _ he ⟨r,ν,rfl,tile,hk⟩
    refine ⟨by light_side,by simp; omega,?_⟩
    have h := Fill.spec K H (d:=d+1) (by omega) (by omega) tile sa.keep sb.keep
    light_call (Meets.of_body (Q:=fun _ μ => x.Done μ (e+1) 0 ∧ Fill.kept x ν μ) text h) with r' ν' ⟨tile',hk'⟩
    light_set (e+1:ℕ)
    exact ⟨r',ν',rfl,tile',hk.trans hk'⟩
  case done => rintro _ ⟨r,ν,rfl,tile,same⟩; exact ⟨by light_side, by simp,tile,same⟩
  case time =>
    have h : ∑ e ∈ Finset.range (x.m-x.t+1), (6 + (tFillList x.L (x.keys e).length + 30)) ≤
        ((List.range (x.m-x.t+1)).map fun e => tFillList x.L (x.keys e).length+60).sum :=
      Finset.sum_le_sum fun _ _ => by omega
    simp only [keys] at h; unfold tTile; simp only [Cond.cost, Expr.cost, keys]; norm_num1; omega

end Tile
end Light.Sec4.BoxTable
