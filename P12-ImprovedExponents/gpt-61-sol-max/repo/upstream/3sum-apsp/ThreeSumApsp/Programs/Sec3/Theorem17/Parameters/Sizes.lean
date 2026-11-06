/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters

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

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Comparing a power with a bound -/

/-- The powers of g, as long as they are below t: the value stays as it is once it has reached
t. -/
def capPow g t
  | 0 => 1
  | i + 1 => if capPow g t i < t then capPow g t i * g else capPow g t i

/-- One more factor. -/
theorem capPow_succ g t i :
    capPow g t (i + 1) = if capPow g t i < t then capPow g t i * g else capPow g t i := rfl

/-- Below t the value is the power, and a value that has reached t shows that the power has. -/
theorem capPow_spec {g} (hg : 1 ≤ g) t i :
    (capPow g t i < t → capPow g t i = g ^ i) ∧ (t ≤ capPow g t i → t ≤ g ^ i) := by
  induction i with
  | zero => simp [capPow]
  | succ i ih =>
    rw [capPow_succ]
    split_ifs with h
    · grind
    · ram_safe

/-- The value is below t exactly if the power is. -/
theorem capPow_lt_iff {g} (hg : 1 ≤ g) t i : capPow g t i < t ↔ g ^ i < t := by
  grind [capPow_spec]


/-- powLt(g, e, t). -/
def powLtBody  :=
  .set 3 (k 0) ;;
  .set 4 (k 1) ;;
  .while (v 3 <' v 1) (
    .ite (v 4 <' v 2) (.set 4 (v 4 *' v 0)) .skip ;;
    .set 3 (v 3 +' k 1)) ;;
  .ite (v 4 <' v 2) (.set 0 (k 1)) (.set 0 (k 0))

/-- **powLt**, for g ≥ 1, returns 1 if g^e < t and 0 if not, in at most 16 e + 14 steps.  It forms
no number above t g + e + 1. -/
theorem powLt_meets {μ} {pPow g e t} (hP : P[pPow]? = some powLtBody) (hg : 1 ≤ g)
    (hword : ((t * g + e + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pPow d [g, e, t] μ (16 * e + 14) fun r μ' =>
      r = (if g ^ e < t then 1 else 0) ∧ μ' = μ := by
  refine .of_body hP ?_
  push_cast at hword
  have  : (0 : ℤ) ≤ (t : ℤ) * g := by positivity
  -- cnt := 0; prod := 1
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while cnt < e.  Before round i, cnt = i and prod = capPow g t i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [g, e, t, i, (capPow g t i : ℕ)], μ⟩) e rfl ?round ?done
    le_rfl) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    rw [capPow_succ]
    generalize capPow g t i = c
    -- if prod < t then prod := prod * g; cnt := cnt + 1
    by_cases hlt : c < t
    · have  := mod_cast Nat.mul_le_mul_right g hlt.le
      exact ⟨by light_side, by light_side, by light_side [hlt],
        by simp [update_frame_setLocal, hlt]⟩
    · exact ⟨by light_side, by light_side, by simp [abs_le, hlt]; omega,
        by simp [update_frame_setLocal, hlt]⟩
  case done =>
    rintro _ rfl
    have hiff := capPow_lt_iff hg t e
    -- return 1 if prod < t, and 0 if not
    refine ⟨by light_side, by light_side,
      Ends.iteLast (fun h => ?_) fun h => ?_ ⟩
    · have hlt := hiff.1 (by simpa using h)
      exact Ends.setTo 1 (by simp [hlt])
    · have hlt : ¬ g ^ e < t := fun h' => h (by simpa using hiff.2 h')
      exact Ends.setTo 0 (by simp [hlt])

/-! ## Roots, rounded up -/


/-- rootCeil(e, t), over the procedure pPow (powLt). -/
def rootCeilBody (pPow : ℕ)  :=
  .set 2 (k 1) ;;
  .call pPow [v 2, v 0, v 1] 3 ;;
  .while (v 3 =' k 1) (
    .set 2 (v 2 +' k 1) ;;
    .call pPow [v 2, v 0, v 1] 3) ;;
  .set 0 (v 2)

/-- The time of rootCeil. -/
def tRootCeil e t := rootCeil e t * (16 * e + 27)

/-- **rootCeil** returns the least g with g^e ≥ t, for e ≥ 1 and t ≥ 1.  It forms no number above t
times the result plus e + 1. -/
theorem rootCeil_meets {μ} {pRoot pPow e t} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (he : e ≠ 0) (ht : 1 ≤ t)
    (hword : ((t * rootCeil e t + e + 1 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pRoot d [e, t] μ (tRootCeil e t) fun r μ' => r = (rootCeil e t : ℕ) ∧ μ' = μ := by
  refine .of_body hR ?_
  have key : ∀ g, g ^ e < t ↔ g < rootCeil e t := fun g => by
    grind [rootCeil_le_iff]
  have hpos : 1 ≤ rootCeil e t := Nat.succ_le_succ (Nat.zero_le _)
  unfold tRootCeil
  generalize rootCeil e t = G at key hpos hword
  obtain ⟨y, rfl⟩ : ∃ y, G = y + 1 := ⟨G - 1, by omega⟩
  have  : y + 1 ≤ t * (y + 1) := Nat.le_mul_of_pos_left _ ht
  -- The test of a candidate g ≤ y + 1.
  have test : ∀ g, 1 ≤ g → g ≤ y + 1 → Meets lim P pPow (d + 1) [g, e, t] μ (16 * e + 14)
      fun r μ' => r = (if g < y + 1 then 1 else 0) ∧ μ' = μ := fun g hg hgy => by

    simpa only [key] using powLt_meets hP hg ((Int.ofNat_le.2 (by
      bound
     : t * g + e + 1 ≤ t * (y + 1) + e + 1)).trans hword)
  -- cand := 1; more := powLt(cand, e, t)
  light_set (1 : ℕ)
  light_call (test 1 le_rfl hpos) with _ μ' ⟨rfl, hμ⟩
  rw [hμ]
  -- while more = 1.  Before round i, cand = i + 1.
  refine Ends.next _ (Ends.whileConst
    (fun i σ => σ = ⟨frame [e, t, (i + 1 : ℕ), if i + 1 < y + 1 then 1 else 0], μ⟩) y (16 * e + 23)
    rfl ?round ?done le_rfl) (by simp; ring_nf; omega)
  case round =>
    rintro i _ hi rfl
    -- cand := cand + 1; more := powLt(cand, e, t)
    refine ⟨by light_side, by simp [hi], Ends.setToThen (i + 1 + 1 : ℕ)
      (Ends.callTo (test (i + 1 + 1) (by omega) (by omega)) ?_)⟩
    rintro _ μ' ⟨rfl, hμ⟩
    simp [hμ]
  case done =>
    rintro _ rfl
    -- return cand
    exact ⟨by light_side, by simp, Ends.setTo (y + 1 : ℕ) (by simp) (hT := by simp; ring_nf; omega)⟩

/-- Rounding a root down is rounding the root of the next number up, minus one. -/
theorem rootCeil_succ {e} (he : e ≠ 0) t : rootCeil e (t + 1) = rootFloor e t + 1 := by
  have h : ∀ g, rootCeil e (t + 1) ≤ g ↔ rootFloor e t + 1 ≤ g := fun g => by
    grind [rootCeil_le_iff, le_rootFloor_iff]
  exact le_antisymm ((h _).2 le_rfl) ((h _).1 le_rfl)

/-! ## The four parameters of the proof of Theorem 19 -/

/-! ## ⌊n²/√D⌋ and quotients rounded up -/

/-- queryCapNat(n, D).  Locals 0 and 1 are the arguments, local 2 is n⁴, local 3 the candidate. -/
def queryCapNatBody :=
  .set 2 (v 0 *' v 0 *' v 0 *' v 0) ;;
  .set 3 (k 0) ;;
  .while ((v 3 +' k 1) *' (v 3 +' k 1) *' v 1 ≤' v 2) (.set 3 (v 3 +' k 1)) ;;
  .set 0 (v 3)

/-- The time of queryCapNat. -/
def tQueryCapNat n D := 18 * queryCapNat n D + 26

/-- The numbers that the test of queryCapNat forms for a candidate c that is at most the result
C. -/
private theorem queryCapNat_test_bounds {n D C c : ℕ} (hD : 1 ≤ D)
    (hmax : (C + 1) * (C + 1) * D ≤ 4 * n ^ 4 + D) (hc : c ≤ C) :
    (c : ℤ) + 1 ≤ ((c : ℤ) + 1) * ((c : ℤ) + 1) ∧
      ((c : ℤ) + 1) * ((c : ℤ) + 1) ≤ ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ∧
      ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ≤ 4 * ((n ^ 4 : ℕ) : ℤ) + D := by
  have  : (c + 1) * (c + 1) * D ≤ (C + 1) * (C + 1) * D :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  exact ⟨by simp_all,
    by light_side,
    by grind⟩

/-- **queryCapNat** returns ⌊n²/√D⌋, for D ≥ 1. -/
theorem queryCapNat_meets {μ} {q n D} (hP : P[q]? = some queryCapNatBody) (hD : 1 ≤ D)
    (hword : ((4 * n ^ 4 + D + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [n, D] μ (tQueryCapNat n D) fun r μ' => r = (queryCapNat n D : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have test : ∀ c , c + 1 ≤ queryCapNat n D ↔
      ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ≤ ((n ^ 4 : ℕ) : ℤ) := fun c =>
    (queryCapNat_succ_le_iff hD c).trans (mod_cast Iff.rfl)
  have bounds := fun c =>
    queryCapNat_test_bounds (c := c) hD (queryCapNat_succ_sq_mul_le (n := n) hD)
  unfold tQueryCapNat
  generalize queryCapNat n D = C at test bounds
  rw [show ((4 * n ^ 4 + D + 2 : ℕ) : ℤ) = 4 * ((n ^ 4 : ℕ) : ℤ) + D + 2 by rfl]
    at hword
  have  : (n : ℤ) * n ≤ ((n ^ 4 : ℕ) : ℤ) := mod_cast show n * n ≤ n ^ 4 by
      rw [show n ^ 4 = n * n * (n * n) by ring]; exact Nat.le_mul_self (n * n)
  have  : (n : ℤ) * n * n ≤ ((n ^ 4 : ℕ) : ℤ) := by
    ram_arith
  have hfour : (n : ℤ) * n * n * n = ((n ^ 4 : ℕ) : ℤ) := by push_cast; ring
  have  : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  have  : (0 : ℤ) ≤ (n : ℤ) * n * n := by positivity
  generalize ((n ^ 4 : ℕ) : ℤ) = N at *
  -- n4 := n⁴; cand := 0
  light_set N using hfour
  light_set (0 : ℕ)
  -- while (cand + 1)² D ≤ n4: cand := cand + 1
  refine Ends.next _ (Ends.whileBlock (fun c σ => σ = ⟨frame [n, D, N, c], μ⟩) C rfl ?round
    ?done le_rfl)
  case round =>
    rintro c _ hc rfl
    have  := bounds c hc.le
    have  := (test c).1 hc
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have  := bounds C le_rfl
    have  := mt (test C).2 (Nat.not_succ_le_self C)
    -- return cand
    exact ⟨by light_side, by light_side, Ends.setTo C (by simp)⟩

/-- ceilDiv(a, b).  Locals 0 and 1 are the arguments, local 2 is the candidate q, local 3 is
q b. -/
def ceilDivBody :=
  .set 2 (k 0) ;;
  .set 3 (k 0) ;;
  .while (v 3 <' v 0) (
    .set 3 (v 3 +' v 1) ;;
    .set 2 (v 2 +' k 1)) ;;
  .set 0 (v 2)

/-- The time of ceilDiv. -/
def tCeilDiv (a b : ℕ) := 12 * (a ⌈/⌉ b) + 10

/-- **ceilDiv** returns ⌈a/b⌉, for b ≥ 1. -/
theorem ceilDiv_meets {μ} {q a b} (hP : P[q]? = some ceilDivBody) (hb : 1 ≤ b)
    (hword : ((a + b + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [a, b] μ (tCeilDiv a b) fun r μ' => r = (a ⌈/⌉ b : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have test : ∀ i, i < a ⌈/⌉ b ↔ i * b < a := fun i => Nat.lt_ceilDiv_iff hb
  unfold tCeilDiv
  generalize a ⌈/⌉ b = q at test
  -- cand := 0; prod := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while prod < a: prod := prod + b; cand := cand + 1.  Before round i, prod = i b.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [a, b, i, (i * b : ℕ)], μ⟩) q (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt := (test i).1 hi
    have hle := Nat.le_mul_of_pos_right i hb
    rw [Nat.succ_mul]
    generalize i * b = m at hlt hle
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have  := mt (test q).2 (lt_irrefl q)
    ram_safe

end Light.Sec3
