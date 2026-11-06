/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters

/-!
# The parameters of Theorems 17 and 19, without division and without roots

The proof of Theorem 19 chooses D as "the largest power of four with D ≤ n^{1/18}"
and g := ⌈D^{1/36}⌉, or D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉; the reduction of Theorem 17 uses
⌊n²/√D⌋ and quotients rounded up.  The language has neither division nor roots, so all of these are
found by counting up.  A power is compared with a bound without forming a number above the bound
times the base.

* powLt(g, e, t), for g ≥ 1, returns 1 if g^e < t, and 0 if not (`powLt_meets`); what it holds after
  i factors is `capPow g t i`.
* rootCeil(e, t) returns the least g with g^e ≥ t (`rootCeil_meets`).
* The four parameters; 5 and 26 stand for the two routes of Theorem 19, through Theorem 5 and
  through Corollary 26.  d5(n) returns the largest power of four that is at most n^{1/18}, g5(D)
  returns ⌈D^{1/36}⌉, d26(n) returns ⌊n^{1/18}⌋, and g26(D) returns ⌈D^{0.0315}⌉; g5 and g26
  are for D ≥ 1 (`d5_spec`, `g5_spec`, `d26_spec`, `g26_spec`).
* queryCapNat(n, D) returns ⌊n²/√D⌋, and ceilDiv(a, b) returns ⌈a/b⌉ (`queryCapNat_meets`,
  `ceilDiv_meets`).

No routine touches the memory.
-/


namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Comparing a power with a bound -/

/-- The powers of g, as long as they are below t: the value stays as it is once it has reached
t. -/
def capPow (g t : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => if capPow g t i < t then capPow g t i * g else capPow g t i

/-- One more factor. -/
theorem capPow_succ (g t i : ℕ) :
    capPow g t (i + 1) = if capPow g t i < t then capPow g t i * g else capPow g t i := rfl

variable {g : ℕ}

/-- Below t the value is the power, and a value that has reached t shows that the power has. -/
theorem capPow_spec (hg : 1 ≤ g) (t i : ℕ) :
    (capPow g t i < t → capPow g t i = g ^ i) ∧ (t ≤ capPow g t i → t ≤ g ^ i) := by
  induction i with
  | zero => aesop
  | succ i ih =>
    rw [capPow_succ]
    split_ifs with h
    · grind
    · exact ⟨by omega,
        fun _ => (ih.2 (not_lt.1 h)).trans (Nat.pow_le_pow_right hg (Nat.le_succ i))⟩

/-- The value is below t exactly if the power is. -/
theorem capPow_lt_iff (hg : 1 ≤ g) (t i : ℕ) : capPow g t i < t ↔ g ^ i < t := by
  grind [capPow_spec]

namespace PowLt

/- The local variables of powLt: the arguments g, e, t; the number of factors so far; their
product (Acc). -/
slots Base Exp Bound Cnt Acc

end PowLt

open PowLt in
/-- powLt(g, e, t). -/
def powLtBody : Stmt :=
  .set Cnt (k 0) ;;
  .set Acc (k 1) ;;
  .while (v Cnt <' v Exp) (
    .ite (v Acc <' v Bound) (.set Acc (v Acc *' v Base)) .skip ;;
    .set Cnt (v Cnt +' k 1)) ;;
  .ite (v Acc <' v Bound) (.set Base (k 1)) (.set Base (k 0))

variable {μ : ℕ → ℤ} {e t pPow : ℕ}

/-- **powLt**, for g ≥ 1, returns 1 if g^e < t and 0 if not, in at most 16 e + 14 steps.  It forms
no number above t g + e + 1. -/
theorem powLt_meets (hP : P[pPow]? = some powLtBody) (hg : 1 ≤ g)
    (hword : ((t * g + e + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pPow d [g, e, t] μ (16 * e + 14) fun r μ' =>
      r = (if g ^ e < t then 1 else 0) ∧ μ' = μ := by
  refine .of_body hP ?_
  light_set 0
  light_set 1
  -- while cnt < e.  Before round i, cnt = i and prod = capPow g t i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [g, e, t, i, (capPow g t i)], μ⟩) e (by rfl) ?_ ?_
    le_rfl) (by simp; omega)
  ·
    rintro i _ hi rfl
    rw [capPow_succ]
    generalize capPow g t i = c
    -- if prod < t then prod := prod * g; cnt := cnt + 1
    by_cases hlt : c < t
    · have hmul : c * g ≤ t * g := by exact_mod_cast Nat.mul_le_mul_right g hlt.le
      exact ⟨by light_side, by light_side, by light_side [hlt],
        by simp_all [update_frame_setLocal]⟩
    · exact ⟨by light_side, by light_side, by simp [abs_le, hlt]; omega,
        by simp [update_frame_setLocal, hlt]⟩
  ·
    rintro _ rfl
    have hiff := capPow_lt_iff hg t e
    -- return 1 if prod < t, and 0 if not
    refine ⟨by light_side, by light_side,
      Ends.iteLast (fun h => ?_) fun h => ?_⟩
    · exact Ends.setTo 1 (by simp_all)
    · exact Ends.setTo 0 (by simp_all)

/-! ## Roots, rounded up -/

namespace RootCeil

/- The local variables of rootCeil: the arguments e, t; the candidate g; whether g^e < t. -/
slots Exp Bound Cand More

end RootCeil

open RootCeil in
/-- rootCeil(e, t), over the procedure pPow (powLt). -/
def rootCeilBody (pPow : ℕ) : Stmt :=
  .set Cand (k 1) ;;
  .call pPow [v Cand, v Exp, v Bound] More ;;
  .while (v More =' k 1) (
    .set Cand (v Cand +' k 1) ;;
    .call pPow [v Cand, v Exp, v Bound] More) ;;
  .set Exp (v Cand)

/-- The time of rootCeil. -/
def tRootCeil (e t : ℕ) : ℕ := rootCeil e t * (16 * e + 27)

/-- **rootCeil** returns the least g with g^e ≥ t, for e ≥ 1 and t ≥ 1.  It forms no number above t
times the result plus e + 1. -/
theorem rootCeil_meets {pRoot : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (he : e ≠ 0) (ht : 1 ≤ t)
    (hword : ((t * rootCeil e t + e + 1 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pRoot d [e, t] μ (tRootCeil e t) fun r μ' => r = (rootCeil e t : ℕ) ∧ μ' = μ := by
  refine .of_body hR ?_
  have key : ∀ g, g ^ e < t ↔ g < rootCeil e t := by grind [not_le, rootCeil_le_iff]
  have hpos : 1 ≤ rootCeil e t := Nat.succ_le_succ (Nat.zero_le _)
  unfold tRootCeil
  generalize rootCeil e t = G at key hpos hword
  obtain ⟨y, rfl⟩ : ∃ y, G = y + 1 := by aesop
  have hyt : y + 1 ≤ t * (y + 1) := by simp_all
  -- The test of a candidate g ≤ y + 1.
  have test : ∀ g, 1 ≤ g → g ≤ y + 1 → Meets lim P pPow (d + 1) [g, e, t] μ (16 * e + 14)
      fun r μ' => r = (if g < y + 1 then 1 else 0) ∧ μ' = μ := fun g hg hgy => by
    have hle : t * g + e + 1 ≤ t * (y + 1) + e + 1 := by
      simp_all [Nat.mul_le_mul_left]
    grind [powLt_meets, Int.ofNat_le]
  -- cand := 1; more := powLt(cand, e, t)
  light_set 1
  light_call (test 1 le_rfl hpos) with _ μ' ⟨rfl, hμ⟩
  rw [hμ]
  -- while more = 1.  Before round i, cand = i + 1.
  refine Ends.next _ (Ends.whileConst
    (fun i σ => σ = ⟨frame [e, t, (i + 1), if i + 1 < y + 1 then 1 else 0], μ⟩) y (16 * e + 23)
    (by simp) ?_ ?_ le_rfl) (by simp; grind)
  ·
    rintro i _ hi rfl
    -- cand := cand + 1; more := powLt(cand, e, t)
    refine ⟨by light_side, by simp_all, Ends.setToThen (i + 1 + 1)
      (Ends.callTo (test (i + 1 + 1) (by omega) (by omega)) ?_)⟩
    simp
  ·
    rintro _ rfl
    -- return cand
    exact ⟨by light_side, by simp, Ends.setTo (y + 1) (by simp)⟩

/-- Rounding a root down is rounding the root of the next number up, minus one. -/
theorem rootCeil_succ (he : e ≠ 0) (t : ℕ) : rootCeil e (t + 1) = rootFloor e t + 1 := by
  have h : ∀ g, rootCeil e (t + 1) ≤ g ↔ rootFloor e t + 1 ≤ g := by grind [rootCeil_le_iff, Nat.succ_le_iff, not_le, le_rootFloor_iff]
  exact le_antisymm (by simp_all) (by grind)

/-! ## The four parameters of the proof of Theorem 19 -/

/-! ## ⌊n²/√D⌋ and quotients rounded up -/

/-- queryCapNat(n, D).  Locals 0 and 1 are the arguments, local 2 is n⁴, local 3 the candidate. -/
def queryCapNatBody : Stmt :=
  .set 2 (v 0 *' v 0 *' v 0 *' v 0) ;;
  .set 3 (k 0) ;;
  .while ((v 3 +' k 1) *' (v 3 +' k 1) *' v 1 ≤' v 2) (.set 3 (v 3 +' k 1)) ;;
  .set 0 (v 3)

/-- The time of queryCapNat. -/
def tQueryCapNat (n D : ℕ) : ℕ := 18 * queryCapNat n D + 26

variable {n D : ℕ}

/-- The numbers that the test of queryCapNat forms for a candidate c that is at most the result
C. -/
theorem queryCapNat_test_bounds {C c : ℕ} (hD : 1 ≤ D)
    (hmax : (C + 1) * (C + 1) * D ≤ 4 * n ^ 4 + D) (hc : c ≤ C) :
    (c : ℤ) + 1 ≤ ((c : ℤ) + 1) * ((c : ℤ) + 1) ∧
      ((c : ℤ) + 1) * ((c : ℤ) + 1) ≤ ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ∧
      ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ≤ 4 * ((n ^ 4 : ℕ) : ℤ) + D := by
  have hmono : (c + 1) * (c + 1) * D ≤ (C + 1) * (C + 1) * D :=
    by simp_all [Nat.mul_le_mul_right, Nat.mul_le_mul]
  exact ⟨by simp,
    by simp_all,
    by grind⟩

variable {q : ℕ}

/-- **queryCapNat** returns ⌊n²/√D⌋, for D ≥ 1. -/
theorem queryCapNat_meets (hP : P[q]? = some queryCapNatBody) (hD : 1 ≤ D)
    (hword : ((4 * n ^ 4 + D + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [n, D] μ (tQueryCapNat n D) fun r μ' => r = (queryCapNat n D : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have test : ∀ c : ℕ, c + 1 ≤ queryCapNat n D ↔
      (c + 1) * (c + 1) * D ≤ ((n ^ 4 : ℕ) : ℤ) := fun c =>
    (queryCapNat_succ_le_iff hD c).trans (by exact_mod_cast Iff.rfl)
  have bounds := fun c =>
    queryCapNat_test_bounds (c := c) hD (queryCapNat_succ_sq_mul_le (n := n) hD)
  unfold tQueryCapNat
  generalize queryCapNat n D = C at test bounds
  rw [show 4 * n ^ 4 + D + 2 = 4 * n ^ 4 + D + 2 by rfl]
    at hword
  have hsq : n * n ≤ n ^ 4 := by
    exact_mod_cast show n * n ≤ n ^ 4 by
      rw [show n ^ 4 = n * n * (n * n) by ring]; simp_all [Nat.le_mul_self]
  have hcube : n * n * n ≤ ((n ^ 4 : ℕ) : ℤ) := by
    exact_mod_cast show n * n * n ≤ n ^ 4 by
      rw [show n ^ 4 = n * n * (n * n) by ring]
      simp_all [Nat.mul_le_mul_left, Nat.le_mul_self]
  have hfour : n * n * n * n = ((n ^ 4 : ℕ) : ℤ) := by grind
  have hsq0 : 0 ≤ n * n := by positivity
  have hcube0 : 0 ≤ (n : ℤ) * n * n := by positivity
  generalize n ^ 4 = N at *
  -- n4 := n⁴; cand := 0
  light_set N using hfour
  light_set 0
  -- while (cand + 1)² D ≤ n4: cand := cand + 1
  refine Ends.next _ (Ends.whileBlock (fun c σ => σ = ⟨frame [n, D, N, c], μ⟩) C (by simp) ?_
    ?_ le_rfl)
  ·
    rintro c _ hc rfl
    have hb := bounds c hc.le
    have hle := (test c).1 hc
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  ·
    rintro _ rfl
    have hb := bounds C le_rfl
    have hnot := mt (test C).2 (Nat.not_succ_le_self C)
    -- return cand
    exact ⟨by light_side, by light_side, Ends.setTo C (by simp)⟩

/-- ceilDiv(a, b).  Locals 0 and 1 are the arguments, local 2 is the candidate q, local 3 is
q b. -/
def ceilDivBody : Stmt :=
  .set 2 (k 0) ;;
  .set 3 (k 0) ;;
  .while (v 3 <' v 0) (
    .set 3 (v 3 +' v 1) ;;
    .set 2 (v 2 +' k 1)) ;;
  .set 0 (v 2)

/-- The time of ceilDiv. -/
def tCeilDiv (a b : ℕ) : ℕ := 12 * (a ⌈/⌉ b) + 10

/-- **ceilDiv** returns ⌈a/b⌉, for b ≥ 1. -/
theorem ceilDiv_meets {a b : ℕ} (hP : P[q]? = some ceilDivBody) (hb : 1 ≤ b)
    (hword : ((a + b + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [a, b] μ (tCeilDiv a b) fun r μ' => r = (a ⌈/⌉ b : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have test : ∀ i, i < a ⌈/⌉ b ↔ i * b < a := by grind [Nat.lt_ceilDiv_iff]
  unfold tCeilDiv
  generalize a ⌈/⌉ b = q at test
  -- cand := 0; prod := 0
  light_set 0
  light_set 0
  -- while prod < a: prod := prod + b; cand := cand + 1.  Before round i, prod = i b.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [a, b, i, (i * b : ℕ)], μ⟩) q (by simp)
    ?_ ?_ le_rfl)
  ·
    rintro i _ hi rfl
    have hlt := (test i).1 hi
    have hle := Nat.le_mul_of_pos_right i hb
    rw [Nat.succ_mul]
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  ·
    rintro _ rfl
    have hnot := mt (test q).2 (lt_irrefl q)
    exact ⟨by light_side, by light_side, Ends.setTo q (by simp)⟩
