/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Parameters
public import ThreeSumApsp.Util.Asymptotics.UpperBounds

/-!
# Running-time claims of Sections 2 to 4, for an abstract notion of "solved in time T"

The paper derives many of its running times from others: "Plug Theorem 19 into Theorem 21", "This is
Corollary 26 with N = n". To check such deductions on their own, this file introduces

* the record `DetTimeModel`: for each problem of Sections 2 to 4 a predicate on running times `T`,
  read as "a deterministic algorithm solves the problem in time `T`", about which nothing is
  assumed (the record `ConditionalTimes.TimeModel` of the three conditional lemmas is another
  one, and nothing links the two);
* two closure properties of the set of running times (namespace `Closure`), which are hypotheses
  like the claims;
* the claims, each as a proposition about `M : DetTimeModel` (namespace `Claim`): time sentences of
  the paper, transfer claims ("if B is solved in time T then A is solved in time extra + calls · T")
  that the paper proves or calls straightforward, and the results it cites from the literature
  (docstrings marked CITED, names starting with an author key, such as `Claim.CH20_Theorem_5_1`).

The lemmas of the files beside this one, such as `Corollary16.of_corollary_26`, are implications
between claims, valid for every `M`. No machine is defined here and no running time is proved here.
They are applied to the interpretation `Light.lightModel`, in which `M.problem T` says that a
procedure of a program of the light language solves the problem within `T` steps; there the lemmas
carry the running times of the programs to the theorems of the paper, and the compiler carries these
to the word RAM.  For that interpretation both closure properties and every claim, at the parameters
of the paper, are proved, the cited results included: the reductions are written as programs
(theorems named `claim_…` and `closure_…`), and the derived claims follow by the lemmas.  So no
statement about the word RAM has a claim as a hypothesis.

Conventions.

* The parameters of a running time.  Sizes (`n`, `N`, `s`) are exact.  `D` is exact for the matrix
  problems (the matrices are `N × D` and `D × N`); for the two triangle problems of Section 3.1 it
  is a declared parameter, given with the input: a graph whose middle part has at most `D` vertices.
  Only `w` and `u` are upper bounds: "at most `w` query pairs (or positions)", "numbers of absolute
  value at most `u`".
* Sizes are at least 1 and bounds `u` on numbers are at least 1.  The value of a running time at
  size 0 or at a bound below 1 has no meaning: `M.problem T` says nothing about it.
* Word length.  The intended machine is the paper's word RAM (Section 2); its words are taken to
  have `Θ(log(size))` bits, and `Θ(log(n + D))` bits for the four problems that have the parameter
  `D`.  Numbers need not fit into one word, since `u` is not bounded in terms of the size: a number
  of absolute value at most `u` takes at most about `1 + log u` words, whatever the size (sizes go
  down to 1), and about `κ` words if `u = n^κ`.  This is why factors `1 + log u` appear in
  overheads.  For `u = n^{O(1)}`, the case of the paper's theorems, these factors are constants or
  logarithms.
* Calls.  As in Section 3 of the paper ("the extra time plus the total time to solve B on each
  instance created"), a transfer claim charges a call of an algorithm exactly its running time, and
  everything else to the extra time.  An algorithm that is called runs on the caller's machine,
  whose words may be longer than its own input would require. Proving the claims for an
  interpretation `M` requires that this is legitimate for `M`.
* The bound `u` on the numbers is an argument of its own, not a function of the size, because
  Theorem 21(b) fixes the bound and lets the size vary.
* `O(·)` with several parameters is written with an explicit constant.  `O(·)` in `n` alone, along
  `u = n^κ`, is `UpperBigOPow`, `UpperPowPolylog` or `UpperPowLittleO`: a running time is only ever
  bounded from above.
-/

@[expose] public section

namespace ThreeSumApsp

/-- An interpretation of "a deterministic algorithm solves the problem in time T", for each problem
of Sections 2 to 4. Each field is a predicate on running times.  The intended meaning of
`M.problem T`: there is a deterministic algorithm that gives a correct answer on every input, and
that takes time at most `T(parameters)` on every input with these parameters (sizes and `D` as
given, at most `w` pairs, numbers at most `u`; sizes and `u` at least 1). -/
structure DetTimeModel where
  /-- Theorem 5: given `X ∈ ℤ^{N×D}`, `Y ∈ ℤ^{D×N}` with entries of absolute value at most
  `u` and a set of at most `w` positions, compute the wanted entries of `XY` (`IsWantedEntries`).
  The arguments of the time are `N D w u`. -/
  thinProduct : (ℕ → ℕ → ℕ → ℝ → ℝ) → Prop
  /-- #Lop-AE-SparseTri(n, D), Definition 14, with at most `w` query pairs
  (`LopInstance.IsCountingAnswer`).  The arguments of the time are `n D w`. -/
  lopCount : (ℕ → ℕ → ℕ → ℝ) → Prop
  /-- Lop-AE-SparseTri(n, D), Definition 13, with at most `w` query pairs
  (`LopInstance.IsDetectionAnswer`).  The arguments of the time are `n D w`. -/
  lopDetect : (ℕ → ℕ → ℕ → ℝ) → Prop
  /-- Exact Triangle on `n` vertices per part with integer weights of absolute value at most `u`
  (`TriangleInstance.HasZeroTriangle`).  The arguments of the time are `n u`. -/
  exactTriangle : (ℕ → ℝ → ℝ) → Prop
  /-- Convolution-3SUM on `N` integers of absolute value at most `u` (`Convolution3SUM`).  Arguments
  `N u`. -/
  convolution3SUM : (ℕ → ℝ → ℝ) → Prop
  /-- 3SUM on `n` integers of absolute value at most `u` (`ThreeSum`).  Arguments `n u`. -/
  threeSum : (ℕ → ℝ → ℝ) → Prop
  /-- The (min,+)-product of two `n × n` integer matrices with entries of absolute value at most `u`
  (`IsMinPlusProduct`). Arguments `n u`. -/
  minPlusProduct : (ℕ → ℝ → ℝ) → Prop
  /-- APSP on directed `n`-vertex graphs with integer weights of absolute value at most `u` and no
  negative cycles (`IsDistanceMatrix`, `NoNegativeCycle`).  Arguments `n u`. -/
  apsp : (ℕ → ℝ → ℝ) → Prop

/-! ## The bounds in `n`, `D` and the number `w` of positions or query pairs -/

namespace Closure

end Closure

namespace Claim

/-! ## Time sentences -/

/-! ## Transfer claims that the paper proves or calls straightforward -/

/-- Proof of Corollary 15: "Apply Theorem 5 with N = n to the two biadjacency matrices".
Writing down the two matrices and copying the answers costs `O(nD + w + 1)`; their entries are 0
and 1. -/
def LopCountFromThinProduct (M : DetTimeModel) : Prop :=
  ∃ C₀ : ℝ, ∀ T : ℕ → ℕ → ℕ → ℝ → ℝ, M.thinProduct T →
    M.lopCount fun n D w => T n D w 1 + C₀ * ((n : ℝ) * (D : ℝ) + (w : ℝ) + 1)

/-- Proof of Corollary 15: the counts "are nonzero exactly for the query pairs that lie in
a triangle". -/
def LopDetectFromCount (M : DetTimeModel) : Prop :=
  ∃ C₀ : ℝ, ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopCount T →
    M.lopDetect fun n D w => T n D w + C₀ * ((w : ℝ) + 1)

/-- For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix
`⌈log₂ n⌉` times in the (min,+)-product yields the distance matrix, and all finite entries that
occur have absolute value at most `nU`, where `U` bounds the edge weights.  The constant `c` allows
for a finite stand-in for the entries `+∞` of the matrices, the term with `C₀` for writing a matrix,
and the `+ 1` for the work that remains when `n = 1`. -/
def ApspFromMinPlus (M : DetTimeModel) : Prop :=
  ∃ c C₀ : ℝ, 1 ≤ c ∧ ∀ T : ℕ → ℝ → ℝ, M.minPlusProduct T →
    M.apsp fun n u =>
      ((Nat.clog 2 n : ℝ) + 1) *
        (T n (c * ((n : ℝ) * u)) + C₀ * ((n : ℝ) ^ 2 * (1 + logU (c * ((n : ℝ) * u)))))

/-! ## Results cited from the literature, in the form needed for Theorem 21 -/

/-! ## Claims that are derived from the ones above -/

/-! ## Bounds in `n` alone, along `u = n^κ` -/

/-- On numbers of absolute value at most `n^κ` the problem is solved deterministically in a time of
the class `Cls a`, for every constant `κ ≥ 0`.  Here `S` is the field of a `DetTimeModel` that
belongs to the problem, and `Cls` is `UpperBigOPow` for `O(n^a)`, `UpperPowPolylog` for
`O(n^a (log n)^{O(1)})` or `UpperPowLittleO` for `n^{a+o(1)}`. -/
def SolvedAlongPow (S : (ℕ → ℝ → ℝ) → Prop) (Cls : (ℕ → ℝ) → ℝ → Prop) (a : ℝ) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ T : ℕ → ℝ → ℝ, S T ∧ Cls (fun n => T n ((n : ℝ) ^ κ)) a

end Claim

end ThreeSumApsp
