/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

public import ThreeSumApsp.Lang.Lib.Rect
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Round

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe

variable {lim : Limits} {P : Program}

namespace Grid
registers [NumValues / Result, Val, Table, Digits, Out0, MaxLen, Levels, Params, Free, Ans,
  Beta, Beta', Hit]
end Grid

open Grid

def probe (pRound : ℕ) (bit : Bool) : Stmt :=
  .call pRound
    [v Beta, v Beta', k (if bit then 1 else 0),
      v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free] Hit ;;
  .ite (v Hit =' k 1) (.set Ans (k 1)) .skip

/-- Test every splitting with a single shared success flag. -/
def gridBody (pRound : ℕ) : Stmt :=
  .set Ans (k 0) ;;
  .for Beta (v Digits) (.for Beta' (v Digits) (probe pRound false ;; probe pRound true)) ;;
  .set Result (v Ans)

private abbrev gridLocals (a : FrontArgs) (f : ℕ) (i j z x : ℤ) : List ℤ :=
  a.vals f ++ [z, i, j, x]

private def seen (a : FrontArgs) (f i j : ℕ) : Prop :=
  (∃ k < i, ∃ l < a.Λ, ∃ b, a.Yes f k l b) ∨ ∃ l < j, ∃ b, a.Yes f i l b

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : FrontArgs} {d f pRound : ℕ} {μ : ℕ → ℤ}

private theorem probe_spec (hRound : RoundSpec lim P pRound T r) (hm : FrontMem μ a)
    (H : GridPre lim r a f 0 (d + 1)) (hw : (a.Λ : ℤ) + 2 ≤ lim.word) (hd : d < lim.depth)
    {i j : ℕ} (hi : i < a.Λ) (hj : j < a.Λ) (b : Bool) (q : Prop) (x : ℤ) :
    Ends lim P d (probe pRound b) ⟨frame (gridLocals a f i j (flag q) x), μ⟩
      (tRound T a.n a.V a.m a.np f + 24) fun σ =>
        ∃ x', σ.loc = frame (gridLocals a f i j (flag (q ∨ a.Yes f i j b)) x') ∧
          KeptBut μ σ.mem a.fr a.A (3 * a.n) := by
  unfold probe
  light_call (hRound a f i j b μ hm hi hj (d + 1) H) using gridLocals with _ ν ⟨rfl, hk⟩
  have hflag := flag_mem (a.Yes f i j b)
  light_if hy hn : a.Yes f i j b using flag_eq_one_iff, gridLocals
  · light_set 1 using gridLocals
    exact ⟨_, by rw [flag_of (Or.inr hy : q ∨ a.Yes f i j b)]; rfl, hk⟩
  · light_skip
    aesop

theorem grid_spec {p : ℕ} (hP : P[p]? = some (gridBody pRound))
    (hRound : RoundSpec lim P pRound T r) : GridSpec lim P p T r := by
  intro a f μ hm d H
  have hv := H.V_pos
  have hl : a.Λ ≤ 2 * a.V := by
    have := Nat.log_lt_self 2 (x := 2 * a.V) (by omega)
    rw [H.lam, Lam]
    omega
  have hw : (a.Λ : ℤ) + 2 ≤ lim.word := by
    have := H.ok.word
    simp [gridNeed] at this
    omega
  have hd : d < lim.depth := by have := H.ok.depth; simp [gridNeed] at this; omega
  have H' : GridPre lim r a f 0 (d + 1) :=
    { H with ok := H.ok.mono le_rfl le_rfl (by simp [gridNeed]; omega) }
  let L (t : ℤ × ℤ) := frame (gridLocals a f 0 0 t.1 t.2)
  let t := tRound T a.n a.V a.m a.np f
  let I i j (x : ℤ × ℤ) ν := x.1 = flag (seen a f i j) ∧ KeptBut μ ν a.fr a.A (3 * a.n)
  refine .of_body hP ?_
  unfold gridBody
  light_set 0 using tGrid
  rw [← frame_append_zeros _ 3]
  refine Ends.next (a.Λ * (a.Λ * (2 * t + 48 + 8) + 14) + 6)
    (Ends.forRect (x := Digits) (y := Digits) (b := 2 * t + 48) L I (0, 0)
      ⟨by simp [seen, flag], .refl⟩ (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)
      ?_ ?_ ?_ (hT := le_rfl)) (by simp [tGrid, t])
  · rintro i j ⟨z, x⟩ ν hi hj ⟨hz, hk⟩
    simp only [I, L, rectLoc, update_frame_setLocal] at *
    subst z
    refine Ends.next (t + 24) ((probe_spec hRound (hm.keptBut hk) H' hw hd hi hj false _ x).mono le_rfl ?_)
      (by omega)
    rintro ⟨loc, ν'⟩ ⟨x', hlf, hk'⟩
    change loc = _ at hlf
    subst loc
    refine (probe_spec hRound (hm.keptBut (hk.trans hk')) H' hw hd hi hj true _ x').mono (by omega) ?_
    rintro _ ⟨x'', hout, hk''⟩
    have eq : (seen a f i j ∨ a.Yes f i j false ∨ a.Yes f i j true) ↔ seen a f i (j + 1) := by
      simp only [seen, Nat.exists_lt_succ_right, Bool.exists_bool, or_assoc]
    exact ⟨(flag (seen a f i (j + 1)), x''), by rw [← flag_congr eq, ← or_assoc]; exact hout,
      rfl, hk.trans (hk'.trans hk'')⟩
  · intro i x ν _ h
    refine ⟨h.1.trans (flag_congr ?_), h.2⟩
    unfold seen
    rw [Nat.exists_lt_succ_right]
    simp
  · rintro ⟨z, x⟩ j ν ⟨hz, hk⟩
    simp only [L, rectLoc, update_frame_setLocal]
    refine Ends.setTo z ?_ (by exact ⟨trivial, rfl⟩) ?_
    all_goals (simp_all [seen, tGrid, t] <;> omega)

end Light.Sec3.ChanHe
