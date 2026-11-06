/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan

/-!
# Brute force (the proof of Theorem 19)

In the proof of Theorem 19, "smaller instances are solved by brute force": the procedure brute
(`bruteBody`) scans all of `C` for every pair `(a, b)` (`brute_spec`, `brute_meets`).  It takes at
most `100 n³ + 100` steps (`brute_solves`).
-/


open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Brute force finds a zero triangle if and only if there is one. -/
theorem hasZero_iff (n : ℕ) (AB BC AC : List ℤ) :
    hasZero n AB BC AC = true ↔ (triOf n AB BC AC).HasZeroTriangle := by
  unfold hasZero TriangleInstance.HasZeroTriangle TriangleInstance.IsZeroTriangle TriangleInstance.S
  simp [List.any_eq_true, List.mem_range, scanHit, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, by assumption⟩
  aesop

/-- Some `b` below `b'` gives a zero triangle with `a`. -/
def bruteRow (n : ℕ) (AB BC AC : List ℤ) (a b' : ℕ) : Bool :=
  (List.range b').any fun b => scanHit n AB BC AC a b 0 n

/-- Some `a` below `a'` is in a zero triangle. -/
def bruteAll (n : ℕ) (AB BC AC : List ℤ) (a' : ℕ) : Bool :=
  (List.range a').any fun a => bruteRow n AB BC AC a n

theorem bruteRow_succ (n : ℕ) (AB BC AC : List ℤ) (a b : ℕ) :
    bruteRow n AB BC AC a (b + 1) = (bruteRow n AB BC AC a b || scanHit n AB BC AC a b 0 n) := by
  grind [bruteRow]

theorem bruteAll_succ (n : ℕ) (AB BC AC : List ℤ) (a : ℕ) :
    bruteAll n AB BC AC (a + 1) = (bruteAll n AB BC AC a || bruteRow n AB BC AC a n) := by
  grind [bruteAll]

namespace Brute

/- The locals of `brute`.  The arguments: `n`, `U`, the addresses of the three arrays, and the free
pointer.  Then the vertices `a` and `b`, the result so far, and the result of a scan. -/
slots Size Bound AdrAB AdrBC AdrAC Free VtxA VtxB Hit Res

end Brute

open Brute in
/-- One pair `(a, b)`: res := scan(ab, bc, ac, n, a, b, 0, n); if res = 1 then hit := 1. -/
def brutePair (pScan : ℕ) : Stmt :=
  .call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, v VtxA, v VtxB, k 0, v Size] Res ;;
  .ite (v Res =' k 1) (.set Hit (k 1)) .skip

open Brute in
/-- The inner loop of brute: all `b` for one `a`. -/
def bruteInner (pScan : ℕ) : Stmt := Stmt.for VtxB (v Size) (brutePair pScan)

open Brute in
/-- brute(n, U, ab, bc, ac, fr); the parameter is the procedure number of `scan`. -/
def bruteBody (pScan : ℕ) : Stmt :=
  .set Hit (k 0) ;; Stmt.for VtxA (v Size) (bruteInner pScan) ;; .set 0 (v Hit)

/-- The time of brute. -/
def tBrute (n : ℕ) : ℕ := 100 * n ^ 3 + 100

/-- What brute needs: sums of three weights, no cells, one call. -/
def bruteNeed (_n U : ℕ) : Need := ⟨3 * U + 1, 0, 1⟩

/-- An instance of Exact Triangle gives `scan` what it assumes. -/
theorem _root_.Light.TriInst.Pre.weights {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Weights lim μ x.ab x.bc x.ac x.n x.U x.AB x.BC x.AC := ⟨hok.space, by exact_mod_cast hok.word, ⟨hpre.lenAB, hpre.segAB, hpre.leAB, hpre.belowAB.trans hok.cells⟩, ⟨hpre.lenBC, hpre.segBC, hpre.leBC, hpre.belowBC.trans hok.cells⟩, ⟨hpre.lenAC, hpre.segAC, hpre.leAC, hpre.belowAC.trans hok.cells⟩⟩

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}

/-- One pair: the result so far takes the scan for `(a, b)` in. -/
theorem brutePair_spec {b : ℕ} {hit : Bool} {r : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hd : d < lim.depth) (ha : a < n) (hb : b < n) :
    Ends lim P d (brutePair pScan) ⟨frame [n, U, ab, bc, ac, fr, a, b, bit hit, r], μ⟩
      (tScan n + 16) fun σ' => ∃ r', σ' = ⟨frame [n, U, ab, bc, ac, fr, a, b,
        bit (hit || scanHit n AB BC AC a b 0 n), r'], μ⟩ := by
  light_facts C C.arrAB C.arrBC C.arrAC
  -- res := scan(ab, bc, ac, n, a, b, 0, n)
  light_call (scan_meets hP C ha hb (c0 := 0) (Nat.zero_add n).le) with _ _ ⟨rfl, rfl⟩
  rw [flag_eq_bit]
  -- if res = 1 then hit := 1
  cases hscan : scanHit n AB BC AC a b 0 n
  · exact Ends.iteLast (by simp_all [bit]) fun _ => Ends.skip ⟨bit false, by simp⟩
  · exact Ends.iteLast (fun _ => Ends.setTo 1 ⟨bit true, by simp_all⟩)
      fun h => by tauto

/-- The inner loop: all `b` for one `a`. -/
theorem bruteInner_spec {b₀ r₀ : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hd : d < lim.depth) (hn : n ≤ lim.space)
    (ha : a < n) :
    Ends lim P d (bruteInner pScan)
      ⟨frame [n, U, ab, bc, ac, fr, a, b₀, bit (bruteAll n AB BC AC a), r₀], μ⟩
      (n * (24 * n + 59) + 6) fun σ' => ∃ r, σ' = ⟨frame [n, U, ab, bc, ac, fr, a, n,
        bit (bruteAll n AB BC AC (a + 1)), r], μ⟩ := by
  have hw := C.hw
  -- for b < n
  refine Ends.for (fun b σ => ∃ r, σ = ⟨frame [n, U, ab, bc, ac, fr, a, b,
    bit (bruteAll n AB BC AC a || bruteRow n AB BC AC a b), r], μ⟩) n (tScan n + 16)
    ?start ?round ?done ?bound (hT := by simp [tScan]; linarith)
  case start => exact ⟨r₀, by simp [update_frame_setLocal, bruteRow]⟩
  case bound =>
    simp_all
  case round =>
    rintro b _ hb - ⟨r, rfl⟩
    apply (brutePair_spec hP C hd ha hb).mono le_rfl
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, r', by simp [update_frame_setLocal, bruteRow_succ, Bool.or_assoc]⟩
  grind [bruteAll_succ]

end

/-- The steps of the two loops of brute are within its time. -/
theorem tBrute_ge (n : ℕ) : n * (1 + (n * (24 * n + 59) + 6) + 7) + 10 ≤ tBrute n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · decide
  · have hsq : n ^ 2 ≤ n ^ 3 := by simp_all [Nat.pow_le_pow_right]
    grind [Nat.le_self_pow, tBrute]

/-- **The brute force.**  In any program that holds `scanBody` as its procedure number `pScan`,
`bruteBody pScan` ends within `tBrute n` steps, decides whether the instance has a zero triangle,
and changes no cell. -/
theorem brute_spec {pScan : ℕ} (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : x.Pre μ fr) (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Ends lim P d (bruteBody pScan) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ (tBrute x.n)
      fun σ' => σ'.loc 0 = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ σ'.mem = μ := by
  have C := hpre.weights hok
  have hw := C.hw
  have hn :=
    (Nat.le_mul_of_pos_left _ hpre.n_pos).trans ((Nat.le_add_left _ _).trans C.arrAB.below)
  have htime := tBrute_ge x.n
  -- hit := 0
  light_set 0
  -- for a < n
  refine Ends.next _ (Ends.for (fun a σ => ∃ b r, σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr, a, b,
    bit (bruteAll x.n x.AB x.BC x.AC a), r], μ⟩) x.n (x.n * (24 * x.n + 59) + 6)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp; omega)
  case start =>
    exact ⟨0, 0, by simpa [update_frame_setLocal, bruteAll, bit] using
      (frame_append_zeros [x.n, x.U, x.ab, x.bc, x.ac, fr, 0, 0, 0] 1).symm⟩
  case bound =>
    simp_all
  case round =>
    rintro a _ ha - ⟨b, r, rfl⟩
    apply (bruteInner_spec hP C hok.depth hn ha).mono le_rfl
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, x.n, r', by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ - ⟨b, r, rfl⟩
    -- return hit
    refine Ends.setTo (bit (hasZero x.n x.AB x.BC x.AC)) ⟨?_, rfl⟩
      (by aesop) (by simp; omega)
    exact (flag_eq_bit _).symm.trans (by grind [flag_congr, hasZero_iff])

/-- The specification of `brute`, for its callers. -/
theorem brute_meets {p pScan : ℕ} (hB : P[p]? = some (bruteBody pScan))
    (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Meets lim P p d [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (tBrute x.n) fun r μ' =>
      r = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ μ' = μ :=
  by grind [Meets.of_body, brute_spec]

/-- **brute** solves Exact Triangle. -/
theorem brute_solves : Solves etTask [bruteBody 1, scanBody] 0 (fun n _ => tBrute n) bruteNeed :=
  ⟨bruteBody 1, rfl, fun _ _ _ x μ fr hpre hok =>
    (brute_spec rfl x μ fr hpre hok).mono le_rfl fun _ h => ⟨h.1, by tauto⟩⟩
