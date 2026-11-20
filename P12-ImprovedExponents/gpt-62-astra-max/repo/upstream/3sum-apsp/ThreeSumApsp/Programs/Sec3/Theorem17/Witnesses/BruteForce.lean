/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan

/-!
# Brute force (the proof of Theorem 19)

In the proof of Theorem 19, "smaller instances are solved by brute force": the procedure brute
(`bruteBody`) scans all of `C` for every pair `(a, b)` (`brute_spec`, `brute_meets`).  It takes at
most `100 n³ + 100` steps (`brute_solves`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Brute

/-- The locals of `brute`.  The arguments: `n`, `U`, the addresses of the three arrays, and the free
pointer.  Then the vertices `a` and `b`, the result so far, and the result of a scan. -/
abbrev Size : ℕ := 0
slots 2 AdrAB AdrBC AdrAC Free VtxA VtxB Hit Res

end Brute

/-- The time of brute. -/
def tBrute (n : ℕ) : ℕ := 100 * n ^ 3 + 100

/-- What brute needs: sums of three weights, no cells, one call. -/
def bruteNeed (_n U : ℕ) : Need := ⟨3 * U + 1, 0, 1⟩

/-- An instance of Exact Triangle gives `scan` what it assumes. -/
theorem _root_.Light.TriInst.Pre.weights {x : TriInst} {μ } {fr } (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Weights lim μ x.ab x.bc x.ac x.n x.U x.AB x.BC x.AC where
  hw := hok.space
  hU := by exact_mod_cast hok.word
  arrAB := ⟨hpre.lenAB, hpre.segAB, hpre.leAB, hpre.belowAB.trans hok.cells⟩
  arrBC := ⟨hpre.lenBC, hpre.segBC, hpre.leBC, hpre.belowBC.trans hok.cells⟩
  arrAC := ⟨hpre.lenAC, hpre.segAC, hpre.leAC, hpre.belowAC.trans hok.cells⟩

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}

end

end Light.Sec3
