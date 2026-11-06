/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Theorem21b.NegativeTriangle

/-!
# Two loops over arrays for the reduction from Negative Triangle to Exact Triangle

[VW13, Theorem 3.3] in the form needed for Theorem 21(b).  The reduction compares
the binary prefixes of shifted weights; the two loops of this file shift the weights and compute the
prefixes, one more bit at a time.

affine(len, src, m, c, dst) writes m · src[i] + c to dst[i] for i < len, in at most 20 len + 6
steps (`affine_meets`).  prefDown(len, q, r, P) makes one step of the computation of the prefixes on
the arrays q and r: it appends the next bit to q[i] and removes it from r[i], for i < len, in at
most 38 len + 6 steps (`prefDown_meets`).  For prefDown the memory after j rounds is written down
(`prefMem`), `prefDownRound_spec` says what one round does, and the loop rule does the rest.  For
m = ±1 and a list that is bounded by U, `affine_meets_of_absLe` has the side conditions in terms
of U.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ### The locals of affine -/

namespace Aff

/-- The number of cells. -/
abbrev Len := 0
/-- The address of the source. -/
abbrev Src := 1
/-- The factor m. -/
abbrev Factor := 2
/-- The summand c. -/
abbrev Shift := 3
/-- The address of the destination. -/
abbrev Dst := 4
/-- The counter i. -/
abbrev Idx := 5

end Aff

open Aff in
/-- affine(len, src, m, c, dst): for i < len, dst[i] := m · src[i] + c. -/
def affineBody  := pass Idx (v Len) (v Dst) (v Factor *' M (v Src +' v Idx) +' v Shift)

/-! ### The locals of prefDown -/


/-- One step on the pair (q[i], r[i]). -/
def prefDownRound  :=
  .set 5 (k 2 *' M (v 2 +' v 4)) ;;
  .ite (v 5 <' v 3)
    (.store (v 1 +' v 4) (k 2 *' M (v 1 +' v 4)) ;; .store (v 2 +' v 4) (v 5))
    (.store (v 1 +' v 4) (k 2 *' M (v 1 +' v 4) +' k 1) ;;
      .store (v 2 +' v 4) (v 5 -' v 3))

/-- prefDown(len, q, r, P): for i < len, one step on (q[i], r[i]). -/
def prefDownBody : Stmt := .for 4 (v 0) prefDownRound

/-- **affine** writes the list of the numbers m x + c, for x in the list at src, to dst, and changes
nothing else. -/
theorem affine_meets {p} (hp : P[p]? = some affineBody) {μ} {src dst} {m c}
    {l} (hl : Seg μ src l) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src + l.length ≤ lim.space) (hdst : dst + l.length ≤ lim.space)
    (hsep : src + l.length ≤ dst ∨ dst + l.length ≤ src)
    (hb : ∀ x ∈ l, |m * x| ≤ lim.word ∧ |m * x + c| ≤ lim.word) :
    Meets lim P p d [l.length, src, m, c, dst] μ (20 * l.length + 6) fun _ μ' =>
      Seg μ' dst (affL m c l) ∧ SameOutside μ μ' dst l.length := by
  refine .of_body hp ?_
  simp only [affineBody, Aff.Len, Aff.Src, Aff.Factor, Aff.Shift, Aff.Dst, Aff.Idx]
  refine Ends.pass (fun i => m * l.getD i 0 + c) (fun j hj => ?_) ?_ hw hdst rfl rfl
  · -- round j reads src[j], which lies outside the cells that are written
    have  : wrote μ dst (fun i => m * l.getD i 0 + c) j (src + j) = l[j] :=
      (wrote_rest (by omega)).trans (hl j hj)
    obtain ⟨hfits, haddr⟩ := Limits.addr_of_lt hw (x := src + j) (by omega)
    simp_all
  · dsimp only
    exact ⟨seg_wrote_map (fun x => m * x + c) l, sameOutside_wrote le_rfl⟩

/-! ### prefDown -/

/-- The memory after j rounds of prefDown: the first j pairs have made their step. -/
def prefMem μ q r Pw (Q R : List ℤ) j :=
  wrote (wrote μ q (fun i => shiftQ Pw (Q.getD i 0) (R.getD i 0)) j) r
    (fun i => shiftR Pw (R.getD i 0)) j

section

variable {μ : Light.Memory} {q r : ℕ} {Pw : ℤ} {Q R : List ℤ} {j : ℕ}

variable (hsep : q + Q.length ≤ r ∨ r + Q.length ≤ q)

include hsep in
/-- A cell of q that has made its step. -/
private theorem prefMem_q_done  (hj : j ≤ Q.length)
    {i} (hi : i < j) :
    prefMem μ q r Pw Q R j (q + i) = shiftQ Pw (Q.getD i 0) (R.getD i 0) :=
  (wrote_rest (by omega)).trans (wrote_done hi)

/-- A cell of r that has made its step. -/
private theorem prefMem_r_done {i} (hi : i < j) :
    prefMem μ q r Pw Q R j (r + i) = shiftR Pw (R.getD i 0) :=
  wrote_done hi

/-- A cell that has not been written (yet). -/
private theorem prefMem_rest {a} (hq : a < q ∨ q + j ≤ a) (hr : a < r ∨ r + j ≤ a) :
    prefMem μ q r Pw Q R j a = μ a :=
  (wrote_rest hr).trans (wrote_rest hq)

include hsep in
/-- What round j writes. -/
private theorem prefMem_succ  (hj : j < Q.length) :
    Function.update (Function.update (prefMem μ q r Pw Q R j) (q + j)
      (shiftQ Pw (Q.getD j 0) (R.getD j 0))) (r + j) (shiftR Pw (R.getD j 0)) =
        prefMem μ q r Pw Q R (j + 1) := by
  unfold prefMem
  rw [update_wrote (by omega), wrote_succ, wrote_succ]

end

/-- What prefDown needs: the two arrays lie in the memory, apart from each other, and the numbers
that are formed fit in a word. -/
structure PrefPre (lim : Limits) (μ : Light.Memory) (q r : ℕ) (Pw : ℤ) (Q R : List ℤ) : Prop where
  segQ : Seg μ q Q
  segR : Seg μ r R
  len : R.length = Q.length
  space : (lim.space : ℤ) ≤ lim.word
  inQ : q + Q.length ≤ lim.space
  inR : r + Q.length ≤ lim.space
  apart : q + Q.length ≤ r ∨ r + Q.length ≤ q
  two_le : 2 ≤ lim.word
  fitsQ : ∀ x ∈ Q, |2 * x| ≤ lim.word ∧ |2 * x + 1| ≤ lim.word
  fitsR : ∀ x ∈ R, |2 * x| ≤ lim.word ∧ |2 * x - Pw| ≤ lim.word

/-- **One round of prefDown** makes the step on the pair (q[j], r[j]) and leaves 2 r[j] in Twice. -/
private theorem prefDownRound_spec {μ} {q r} {Pw} {Q R}
    (C : PrefPre lim μ q r Pw Q R) {j} (hj : j < Q.length) s :
    Ends lim P d prefDownRound ⟨frame [Q.length, q, r, Pw, j, s], prefMem μ q r Pw Q R j⟩
      prefDownRound.blockCost fun σ' =>
        σ' = ⟨frame [Q.length, q, r, Pw, j, 2 * R.getD j 0], prefMem μ q r Pw Q R (j + 1)⟩ := by
  have hlen := C.len
  have  := C.space
  have  := C.inQ
  have  := C.inR
  have hsep := C.apart

  have hreadQ : prefMem μ q r Pw Q R j (q + j) = Q.getD j 0 :=
    (prefMem_rest (by omega) (by omega)).trans (C.segQ.getD hj 0)
  have hreadR : prefMem μ q r Pw Q R j (r + j) = R.getD j 0 :=
    (prefMem_rest (by omega) (by omega)).trans (C.segR.getD (hlen ▸ hj) 0)
  obtain ⟨hQ2, hQ3⟩ := C.fitsQ _ (List.getD_eq_getElem Q 0 hj ▸ List.getElem_mem hj)
  obtain ⟨hR2, hR3⟩ :=
    C.fitsR _ (List.getD_eq_getElem R 0 (hlen ▸ hj) ▸ List.getElem_mem (hlen ▸ hj))
  have hnext := prefMem_succ (μ := μ) (Pw := Pw) (R := R) hsep hj
  -- from here on x = q[j] and y = r[j]
  generalize Q.getD j 0 = x at hreadQ hQ2 hQ3 hnext
  generalize R.getD j 0 = y at hreadR hR2 hR3 hnext ⊢
  rw [abs_mul, abs_two] at hQ2 hR2
  rw [abs_le] at hQ3 hR3
  unfold prefDownRound
  -- Twice := 2 * mem[ArrR + Idx]
  refine Ends.setToThen (2 * y) ?_ (by simp [Limits.Addr, abs_le, hreadR]; omega)
  -- if Twice < Power
  refine Ends.iteLast (fun hc => ?_) fun hc => ?_
  · have hc' := by simpa using hc
    rw [shiftQ, shiftR, if_pos hc', if_pos hc'] at hnext
    -- mem[ArrQ + Idx] := 2 * mem[ArrQ + Idx]
    refine Ends.storeToThen (q + j) (2 * x) ?_
      (by simp [Limits.Addr, abs_le, hreadQ]; omega)
    -- mem[ArrR + Idx] := Twice
    light_store (r + j) (2 * y)
    exact by rw [hnext]; rfl
  · have hc' : ¬ 2 * y < Pw := by simpa using hc
    rw [shiftQ, shiftR, if_neg hc', if_neg hc'] at hnext
    -- mem[ArrQ + Idx] := 2 * mem[ArrQ + Idx] + 1
    refine Ends.storeToThen (q + j) (2 * x + 1) ?_
      (by simp [Limits.Addr, abs_le, hreadQ]; omega)
    -- mem[ArrR + Idx] := Twice - Power
    light_store (r + j) (2 * y - Pw)
    exact by rw [hnext]; rfl

/-- **prefDown** makes one step on every pair (q[i], r[i]), and changes nothing else. -/
theorem prefDown_meets {p} (hp : P[p]? = some prefDownBody) {μ} {q r} {Pw}
    {Q R} (C : PrefPre lim μ q r Pw Q R) :
    Meets lim P p d [Q.length, q, r, Pw] μ (38 * Q.length + 6) fun _ μ' =>
      Seg μ' q (List.zipWith (shiftQ Pw) Q R) ∧ Seg μ' r (R.map (shiftR Pw)) ∧
        ∀ a, a < q ∨ q + Q.length ≤ a → a < r ∨ r + Q.length ≤ a → μ' a = μ a := by
  refine .of_body hp ?_
  have  := C.len
  have  := C.apart
  have  : (Q.length : ℤ) ≤ lim.word :=
    le_trans (by ram_arith) C.space
  refine Ends.forShape (fun j s μ' => ⟨frame [Q.length, q, r, Pw, j, s], μ'⟩)
    (fun j μ' => μ' = prefMem μ q r Pw Q R j) Q.length prefDownRound.blockCost 0
    (by ram_arith [prefMem, wrote_zero]) ?round ?done
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 1).symm)
    (hT := by simp [prefDownRound]; omega)
  case round =>
    rintro j s _ hj rfl
    exact (prefDownRound_spec C hj s).mono le_rfl fun _ h => ⟨_, _, h, rfl⟩
  case done =>
    rintro s _ rfl
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun a ha hb => prefMem_rest ha hb⟩
    · grind [prefMem_q_done]
    · grind [prefMem_r_done]

/-! ## affine with the factor ± 1 on a list with bounded entries -/

end Light.Sec3
