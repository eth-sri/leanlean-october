/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Slots

public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Instances

/-!
# Scanning a piece (the proof of Theorem 17)

"For every query pair that the oracle accepts, scan the piece C_k of its instance for a c with
S(a,b,c) = 0".  The procedure scan (`scanBody`) goes through an interval of vertices `c` for a fixed
pair `(a, b)` (`scan_spec`, `scan_meets`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- A truth value as a number: 1 for true, 0 for false. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

theorem flag_eq_bit (b : Bool) : flag (b = true) = bit b := by
  cases b
  · simp [bit, flag_of_not]
  · simp [bit, flag_of]

/-! ## The three arrays of weights -/

/-- What `scan` assumes: the three arrays of `n²` weights of absolute value at most `U` lie in the
memory, an address fits in a word, and so does a sum of three weights. -/
structure Weights (lim : Limits) (μ : ℕ → ℤ) (ab bc ac n U : ℕ) (AB BC AC : List ℤ) : Prop where
  hw : lim.space ≤ lim.word
  hU : 3 * U + 1 ≤ lim.word
  arrAB : ArrayAt μ ab AB (n * n) U lim.space
  arrBC : ArrayAt μ bc BC (n * n) U lim.space
  arrAC : ArrayAt μ ac AC (n * n) U lim.space

/-! ## Scanning an interval of vertices -/

namespace Scan

/-- The locals of `scan`.  The arguments: the addresses of the three arrays, `n`, the pair `(a, b)`,
the first vertex `c0` and the number `len` of vertices of the interval.  Then the counter `c`, the
result so far, the weight `w(a,b)`, and the addresses of `w(b, c0)` and of `w(a, c0)`. -/
slots 0 AdrAB AdrBC AdrAC Size VtxA VtxB First Len Cnt Hit Wab RowB RowA

end Scan

open Scan in
/-- One round of `scan`: if `w(a,b) + w(b, c0 + c) + w(a, c0 + c) = 0` then hit := 1; c := c + 1. -/
def scanRound : Stmt :=
  .ite (v Wab +' M (v RowB +' v Cnt) +' M (v RowA +' v Cnt) =' k 0) (.set Hit (k 1)) .skip ;;
  .set Cnt (v Cnt +' k 1)

open Scan in
/-- scan(ab, bc, ac, n, a, b, c0, len). -/
def scanBody : Stmt :=
  .set Hit (k 0) ;;
  .set Wab (M (v AdrAB +' v VtxA *' v Size +' v VtxB)) ;;
  .set RowB (v AdrBC +' v VtxB *' v Size +' v First) ;;
  .set RowA (v AdrAC +' v VtxA *' v Size +' v First) ;;
  .set Cnt (k 0) ;;
  .while (v Cnt <' v Len) scanRound ;;
  .set 0 (v Hit)

/-- The time of scan. -/
def tScan (len : ℕ) : ℕ := 24 * len + 35

/-- One more vertex in a scan. -/
theorem scanHit_succ (n : ℕ) (AB BC AC : List ℤ) (a b c0 c : ℕ) :
    scanHit n AB BC AC a b c0 (c + 1) = (scanHit n AB BC AC a b c0 c || decide
      (AB.getD (a * n + b) 0 + BC.getD (b * n + c0 + c) 0 + AC.getD (a * n + c0 + c) 0 = 0)) := by
  simp [scanHit, List.range_succ]

/-- One round of `scan`, for the weights `wbc` and `wac` that it reads. -/
theorem scanRound_runs {μ} {ab bc ac n a b c0 len c rowB rowA U : ℕ} {wab wbc wac : ℤ}
    {hit} (hw : lim.space ≤ lim.word) (hU : 3 * U + 1 ≤ lim.word)
    (hreadB : μ (rowB + c) = wbc) (hreadA : μ (rowA + c) = wac) (hB : rowB + c < lim.space)
    (hA : rowA + c < lim.space) (leAB : |wab| ≤ U) (leBC : |wbc| ≤ U) (leAC : |wac| ≤ U) :
    scanRound.Runs lim ⟨frame [ab, bc, ac, n, a, b, c0, len, c, bit hit, wab, rowB, rowA], μ⟩
      (· = ⟨frame [ab, bc, ac, n, a, b, c0, len, (c + 1 : ℕ),
        bit (hit || decide (wab + wbc + wac = 0)), wab, rowB, rowA], μ⟩) := by
  rw [abs_le] at leAB leBC leAC
  by_cases hz : wab + wbc + wac = 0 <;>
    exact ⟨by
      simp [scanRound, Limits.Addr, abs_le, hreadB, hreadA, hz]; omega,
      by simp [scanRound, update_frame_setLocal, hreadB, hreadA, hz, bit]⟩

/-- **scan** returns 1 if some `c` in the interval has `S(a,b,c) = 0`, and 0 if not; it changes no
cell. -/
theorem scan_spec {μ} {ab bc ac n a b c0 len U} {AB BC AC}
    (C : Weights lim μ ab bc ac n U AB BC AC) (ha : a < n) (hb : b < n) (hc : c0 + len ≤ n) :
    Ends lim P d scanBody ⟨frame [ab, bc, ac, n, a, b, c0, len], μ⟩ (tScan len) fun σ' =>
      σ'.loc 0 = flag (scanHit n AB BC AC a b c0 len = true) ∧ σ'.mem = μ := by
  light_facts C C.arrAB C.arrBC C.arrAC
  have iab := Nat.mul_add_lt_mul ha hb
  have ibc := Nat.mul_add_le_mul hb hc
  have iac := Nat.mul_add_le_mul ha hc
  -- The weight `w(a,b)` and the addresses of `w(b,c0)` and `w(a,c0)`.
  obtain ⟨wab, hwab⟩ : ∃ z, z = AB.getD (a * n + b) 0 := ⟨_, rfl⟩
  obtain ⟨rowB, hrowB⟩ : ∃ r, r = bc + b * n + c0 := ⟨_, rfl⟩
  obtain ⟨rowA, hrowA⟩ : ∃ r, r = ac + a * n + c0 := ⟨_, rfl⟩
  have hreadAB := (C.arrAB.read iab).trans hwab.symm
  have haddrAB : ((ab : ℤ) + a * n + b).toNat = ab + (a * n + b) := by
    omega
  have leAB := hwab ▸ AbsLe.abs_getD_le (by omega) C.arrAB.bound _
  unfold scanBody tScan
  -- hit := 0; wab := ab[a n + b]; rowB := bc + b n + c0; rowA := ac + a n + c0; c := 0
  light_set 0
  light_set wab using haddrAB, hreadAB
  light_set rowB
  light_set rowA
  light_set 0
  -- while c < len
  refine Ends.next _ (Ends.whileBlock (fun c σ => σ = ⟨frame [ab, bc, ac, n, a, b, c0, len, c,
    bit (scanHit n AB BC AC a b c0 c), wab, rowB, rowA], μ⟩) len ?start ?round ?done le_rfl)
    (by simp [scanRound]; omega)
  case start => rfl
  case round =>
    rintro c _ hcl rfl
    have hreadBC : μ (rowB + c) = BC.getD (b * n + c0 + c) 0 := by
      rw [← C.arrBC.read (by omega), hrowB, Nat.add_assoc bc, Nat.add_assoc bc]
    have hreadAC : μ (rowA + c) = AC.getD (a * n + c0 + c) 0 := by
      rw [← C.arrAC.read (by omega), hrowA, Nat.add_assoc ac, Nat.add_assoc ac]
    refine ⟨by simp, by light_side, ?_⟩
    rw [scanHit_succ, ← hwab]
    exact scanRound_runs C.hw C.hU hreadBC hreadAC (by omega) (by omega) leAB
      (AbsLe.abs_getD_le (Int.natCast_nonneg U) C.arrBC.bound _)
      (AbsLe.abs_getD_le (Int.natCast_nonneg U) C.arrAC.bound _)
  case done =>
    rintro _ rfl
    -- return hit
    exact ⟨by simp, by simp, Ends.setTo (bit (scanHit n AB BC AC a b c0 len))
      ⟨(flag_eq_bit _).symm, rfl⟩ (hT := by simp [scanRound]; omega)⟩

/-- The specification of `scan`, for its callers. -/
theorem scan_meets {p} {μ} {ab bc ac n a b c0 len U} {AB BC AC}
    (hP : P[p]? = some scanBody) (C : Weights lim μ ab bc ac n U AB BC AC) (ha : a < n) (hb : b < n)
    (hc : c0 + len ≤ n) :
    Meets lim P p d [ab, bc, ac, n, a, b, c0, len] μ (tScan len) fun r μ' =>
      r = flag (scanHit n AB BC AC a b c0 len = true) ∧ μ' = μ :=
  Meets.of_body hP (scan_spec C ha hb hc)

end Light.Sec3
