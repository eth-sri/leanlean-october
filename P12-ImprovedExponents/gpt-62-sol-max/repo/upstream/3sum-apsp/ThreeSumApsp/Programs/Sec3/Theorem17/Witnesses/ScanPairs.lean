/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan

/-!
# Reading the answers of one instance and scanning for witnesses

Proof of Theorem 17: "For every query pair that the oracle accepts, scan the piece C_k of its
instance for a c with S(a,b,c) = 0 [...].  We stop as soon as a zero triangle is found."

scanPairs(out, qa, qb, w, f, ab, bc, ac, n, c0, len): for every query pair number `i < w` whose
answer `out[i]` is not 0, scan the piece `{c0, …, c0 + len - 1}` for a zero triangle through the
pair `(qa[i], qb[i])`, as long as none has been found (`f = 0`).  The result is the new value of `f`
(`scanPairs_spec`).  No scan is made after the first successful one, so the number of scans is at
most the number of failed scans plus one (`execsUpto_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits}

/-! ## The pure side -/

/-- The number of accepted pairs among the first w whose scan would fail. -/
def failsUpto (acc hit : ℕ → Bool) (w : ℕ) : ℕ :=
  ((List.range w).filter fun i => acc i && !hit i).length

theorem failsUpto_succ (acc hit : ℕ → Bool) (w : ℕ) :
    failsUpto acc hit (w + 1) = failsUpto acc hit w + (if acc w && !hit w then 1 else 0) := by
  simp only [failsUpto, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

/-! ## The routine -/

/-- What `scanPairs` assumes about the answers of the solver and the `w` query pairs of an instance:
three arrays in the memory, and the query pairs are pairs of vertices. -/
structure Answers (lim : Limits) (μ : ℕ → ℤ) (out qa qb w n : ℕ) (OUT : List ℤ) (QA QB : List ℕ) :
    Prop where
  arrOUT : ListAt μ out OUT w lim.space
  arrQA : IndexAt μ qa QA w n lim.space
  arrQB : IndexAt μ qb QB w n lim.space
  w_lt : w < lim.space

section

variable {μ : ℕ → ℤ} {out qa qb w n c0 len : ℕ} {OUT AB BC AC : List ℤ} {QA QB : List ℕ}

/-- The answer for the query pair number `i` is not 0. -/
abbrev accOf (OUT : List ℤ) (i : ℕ) : Bool := decide (OUT.getD i 0 ≠ 0)

/-- The scan for the query pair number `i` succeeds. -/
abbrev hitOf (n : ℕ) (AB BC AC : List ℤ) (QA QB : List ℕ) (c0 len i : ℕ) : Bool :=
  scanHit n AB BC AC (QA.getD i 0) (QB.getD i 0) c0 len

end

end Light.Sec3
