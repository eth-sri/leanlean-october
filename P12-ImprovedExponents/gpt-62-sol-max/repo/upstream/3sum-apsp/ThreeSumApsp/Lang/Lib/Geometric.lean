/-
Released under Apache 2.0 license, as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.Symbolic
public import ThreeSumApsp.Lang.Lib.Pass
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d dst p len : ℕ} {μ : ℕ → ℤ}

namespace Geometric

registers [Dst, Base, Len, Exp, Entry]

end Geometric

open Geometric

/-- A constant-ratio table. The factor 2 can be formed by addition without loading a literal. -/
def geomTable (b : ℕ) : Stmt :=
  .set Exp (k 0) ;; .set Entry (v Base) ;; .store (v Dst) (v Entry) ;;
  .while (v Exp <' v Len) (
    .set Entry (if b = 2 then v Entry +' v Entry else k b *' v Entry) ;;
    .set Exp (v Exp +' k 1) ;; .store (v Dst +' v Exp) (v Entry))

abbrev geomTime (len : ℕ) := 17 * len + 11

def geomList (b p len : ℕ) : List ℤ := (List.range (len + 1)).map fun j => ((b ^ j * p : ℕ) : ℤ)

/-- Write `p, bp, …, b^len p` in consecutive cells. -/
theorem geomTable_spec {b : ℕ} (hb : 1 ≤ b) (hconst : b ≠ 2 → (b : ℤ) ≤ lim.word)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + (len + 1) ≤ lim.space)
    (hp : ((b ^ len * p : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d (geomTable b) ⟨frame [dst, p, len], μ⟩ (geomTime len) fun σ' =>
      Seg σ'.mem dst (geomList b p len) ∧ SameOutside μ σ'.mem dst (len + 1) := by
  let f (j : ℕ) : ℤ := ((b ^ j * p : ℕ) : ℤ)
  have hfit (j : ℕ) (hj : j ≤ len) : f j ≤ lim.word := by
    exact (Nat.cast_le.2 (Nat.mul_le_mul_right p (Nat.pow_le_pow_right hb hj))).trans hp
  unfold geomTable geomTime
  light_steps
  let I (j : ℕ) (σ : State) := σ = ⟨frame [dst, p, len, j, f j], wrote μ dst f (j + 1)⟩
  refine Ends.whileBlock I len ?_ ?_ ?_ (by split <;> light_time)
  · simpa [I, f, wrote_zero] using (congrArg
      (State.mk (frame [dst, p, len, 0, p])) (wrote_succ (μ := μ) (dst := dst) (f := f) (j := 0)))
  · rintro j _ hj rfl
    have h1 := hfit j hj.le
    have h2 := hfit (j + 1) hj
    have hstep : f (j + 1) = (b : ℤ) * f j := by simp [f, pow_succ, mul_left_comm, mul_comm]
    have h0 : 0 ≤ f j := by positivity
    have hm : 0 ≤ (b : ℤ) * f j := by positivity
    simp only [I]
    rw [← wrote_succ (j := j + 1), hstep]
    rw [hstep] at h2
    have ha : ((dst : ℤ) + ((j : ℤ) + 1)).toNat = dst + (j + 1) := by omega
    refine ⟨by light_side, by light_side, ?_, ?_⟩
    · by_cases h : b = 2
      · subst_vars; light_side
      · light_side [hconst, h]
    · by_cases h : b = 2
      · subst b
        simp [update_frame_setLocal, ha, two_mul]
      · simp [h, update_frame_setLocal, ha]
  · rintro _ rfl
    exact ⟨by light_side, by light_side,
      seg_wrote (by simp [geomList]) (fun i hi => by simp [geomList, f]), sameOutside_wrote le_rfl⟩

end Light
