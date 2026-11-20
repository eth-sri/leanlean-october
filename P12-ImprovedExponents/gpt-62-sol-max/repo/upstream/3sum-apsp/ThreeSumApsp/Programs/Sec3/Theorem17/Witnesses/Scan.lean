/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

public import ThreeSumApsp.Lang.Lib.Any

public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Instances

/-!
# Scanning a piece (the proof of Theorem 17)

"For every query pair that the oracle accepts, scan the piece C_k of its instance for a c with
S(a,b,c) = 0".  The procedure scan (`scanBody`) goes through an interval of vertices `c` for a fixed
pair `(a, b)` (`scan_meets`).
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
structure Weights (lim : Limits) (μ : ℕ → ℤ) (x : TriInst) : Prop
    extends x.Arrays μ lim.space where
  hw : (lim.space : ℤ) ≤ lim.word
  hU : 3 * (x.U : ℤ) + 1 ≤ lim.word

/-- Preserve the scan contract across a write disjoint from the three weight matrices. -/
theorem Weights.keep {x : TriInst} {μ μ' : ℕ → ℤ} {dst len : ℕ} (C : Weights lim μ x)
    (hs : SameOutside μ μ' dst len) (hAB : Apart dst len x.ab (x.n * x.n))
    (hBC : Apart dst len x.bc (x.n * x.n)) (hAC : Apart dst len x.ac (x.n * x.n)) :
    Weights lim μ' x := by
  have := C.arrBC.len
  have := C.arrAC.len
  exact { C with arrAB := C.arrAB.keep, arrBC := C.arrBC.keep, arrAC := C.arrAC.keep }

/-! ## Scanning an interval of vertices -/

namespace Scan

/-- The locals of `scan`.  The arguments: the addresses of the three arrays, `n`, the pair `(a, b)`,
the first vertex `c0` and the number `len` of vertices of the interval.  Then the counter `c`, the
result so far, the weight `w(a,b)`, and the addresses of `w(b, c0)` and of `w(a, c0)`. -/
registers [AdrAB, AdrBC, AdrAC, Size, VtxA, VtxB, First, Len, Cnt, Hit, Wab, RowB, RowA]

end Scan

open Scan in
def scanTest : Cond :=
  v Wab +' M (v RowB +' v Cnt) +' M (v RowA +' v Cnt) =' k 0

open Scan in
/-- scan(ab, bc, ac, n, a, b, c0, len). -/
def scanBody : Stmt :=
  .set Wab (M (v AdrAB +' v VtxA *' v Size +' v VtxB)) ;;
  .set RowB (v AdrBC +' v VtxB *' v Size +' v First) ;;
  .set RowA (v AdrAC +' v VtxA *' v Size +' v First) ;;
  anyPass Cnt Len Hit scanTest ;;
  .set 0 (v Hit)

/-- The time of scan. -/
def tScan (len : ℕ) : ℕ := 24 * len + 35

open Scan in
/-- **scan** returns 1 if some `c` in the interval has `S(a,b,c) = 0`, and 0 if not; it changes no
cell. -/
theorem scan_meets {p : ℕ} {μ : ℕ → ℤ} {x : TriInst} {a b c0 len : ℕ}
    (hP : P[p]? = some scanBody) (C : Weights lim μ x) (ha : a < x.n) (hb : b < x.n)
    (hc : c0 + len ≤ x.n) :
    Meets lim P p d [x.ab, x.bc, x.ac, x.n, a, b, c0, len] μ (tScan len) fun r μ' =>
      r = flag (scanHit x.n x.AB x.BC x.AC a b c0 len = true) ∧ μ' = μ := by
  refine .of_body hP ?_;
  light_facts C C.arrAB C.arrBC C.arrAC
  have iab : a * x.n + b < x.n * x.n := Nat.mul_add_lt_mul ha hb
  have ibc : b * x.n + (c0 + len) ≤ x.n * x.n := Nat.mul_add_le_mul hb hc
  have iac : a * x.n + (c0 + len) ≤ x.n * x.n := Nat.mul_add_le_mul ha hc
  -- The weight `w(a,b)` and the addresses of `w(b,c0)` and `w(a,c0)`.
  obtain ⟨wab, hwab⟩ : ∃ z, z = x.AB.getD (a * x.n + b) 0 := ⟨_, rfl⟩
  obtain ⟨rowB, hrowB⟩ : ∃ r, r = x.bc + b * x.n + c0 := ⟨_, rfl⟩
  obtain ⟨rowA, hrowA⟩ : ∃ r, r = x.ac + a * x.n + c0 := ⟨_, rfl⟩
  have hreadAB : μ (x.ab + (a * x.n + b)) = wab := (C.arrAB.read iab).trans hwab.symm
  have haddrAB : ((x.ab : ℤ) + (a : ℤ) * (x.n : ℤ) + (b : ℤ)).toNat = x.ab + (a * x.n + b) := by
    omega
  have leAB : |wab| ≤ x.U := hwab ▸ AbsLe.abs_getD_le (Int.natCast_nonneg x.U) C.arrAB.bound _
  unfold scanBody tScan
  light_set wab using haddrAB, hreadAB
  light_set rowB
  light_set rowA
  let p c := wab + x.BC.getD (b * x.n + c0 + c) 0 + x.AC.getD (a * x.n + c0 + c) 0 = 0
  have hp : flag (∃ c < len, p c) = flag (scanHit x.n x.AB x.BC x.AC a b c0 len = true) := by
    apply flag_congr
    simp [p, hwab, scanHit, List.any_eq_true]
  refine Ends.pieceThen (R := fun σ => σ.loc Hit = flag (∃ c < len, p c) ∧ σ.mem = μ)
    (Ends.anyPass (T := 24 * len + 8) scanTest p ?_ (by simp) rfl (by omega) (by omega)
      (hT := by light_time [scanTest])) ?_
  · intro c hcl
    have hreadBC : μ (rowB + c) = x.BC.getD (b * x.n + c0 + c) 0 := by
      rw [← C.arrBC.read (by omega), hrowB, Nat.add_assoc x.bc, Nat.add_assoc x.bc]
    have hreadAC : μ (rowA + c) = x.AC.getD (a * x.n + c0 + c) 0 := by
      rw [← C.arrAC.read (by omega), hrowA, Nat.add_assoc x.ac, Nat.add_assoc x.ac]
    have leBC := AbsLe.abs_getD_le (Int.natCast_nonneg x.U) C.arrBC.bound (b * x.n + c0 + c)
    have leAC := AbsLe.abs_getD_le (Int.natCast_nonneg x.U) C.arrAC.bound (a * x.n + c0 + c)
    rw [abs_le] at leAB leBC leAC
    simp only [List.getD_eq_getElem?_getD] at leBC leAC
    light_side [scanTest, hreadBC, hreadAC, p]
  · rintro ⟨loc', _⟩ ⟨hres, rfl⟩
    exact Ends.setLast ⟨by simpa using hres.trans hp, rfl⟩

end Light.Sec3
