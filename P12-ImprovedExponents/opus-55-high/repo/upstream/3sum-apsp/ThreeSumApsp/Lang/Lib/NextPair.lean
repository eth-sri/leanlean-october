/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Lang.Frames
import ThreeSumApsp.Util.Index

/-!
# From a pair to the next pair

A loop that runs through the pairs (a, b) with a, b < n in the order of their numbers t = a n + b
keeps a = t / n and b = t % n in two local variables, so that no division is needed.
`nextPair A B N` is the step from one pair to the next, and `Ends.nextPair` is its rule.
-/


namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- b := b + 1; if b = n then b := 0; a := a + 1.  The locals A, B and N hold a, b and n. -/
def nextPair (A B N : ℕ) : Stmt :=
  .set B (v B +' k 1) ;; .ite (v B =' v N) (.set B (k 0) ;; .set A (v A +' k 1)) .skip

/-- **From the pair number t to the pair number t + 1.** -/
theorem Ends.nextPair {A B N n t T : ℕ} {l : List ℤ} {μ : ℕ → ℤ} {Q : State → Prop}
    (h : Q ⟨frame (setLocal (setLocal l B ((t + 1) % n : ℕ)) A ((t + 1) / n : ℕ)), μ⟩)
    (hn : 0 < n) (ht : ((t + 1 : ℕ) : ℤ) ≤ lim.word) (hnw : (n : ℤ) ≤ lim.word)
    (hA : frame l A = (t / n : ℕ)) (hB : frame l B = (t % n : ℕ)) (hN : frame l N = n)
    (hAB : A ≠ B := by decide) (hBN : N ≠ B := by decide) (hT : 14 ≤ T := by light_time) :
    Ends lim P d (nextPair A B N) ⟨frame l, μ⟩ T Q := by
  have hmod := t.mod_lt hn
  have hdiv := t.div_le_self n
  have hlast := Nat.succ_div_mod_of_eq (n := n) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (i := t) hn
  generalize t / n = a at *
  generalize t % n = b at *
  -- b := b + 1
  refine Ends.setToThen (b + 1 : ℕ) ?_ (by light_norm [Expr.Gives, hB, abs_le]; omega)
    (by simp; omega)
  -- if b = n then b := 0; a := a + 1
  refine Ends.iteLast (fun he => ?_) (fun he => ?_) ⟨trivial, trivial⟩ (by simp; omega)
  · have he : b + 1 = n := by
      have : ((b + 1 : ℕ) : ℤ) = n := by
        simpa only [Cond.Holds, Expr.val, frame_setLocal, if_pos, if_neg hBN, hN] using he
      omega
    refine Ends.setToThen 0 (Ends.setTo (a + 1) ?_
      (by light_norm [Expr.Gives, frame_setLocal, if_neg hAB, hA, abs_le]; omega)
      (by simp; omega)) (by light_norm [Expr.Gives]; omega) (by simp; omega)
    convert h using 2
    grind [frame_setLocal]
  · have he := fun e => he (by
      simp only [Cond.Holds, Expr.val, frame_setLocal, if_pos]
      omega)
    apply Ends.skip
    convert h using 2
    grind [frame_setLocal]
