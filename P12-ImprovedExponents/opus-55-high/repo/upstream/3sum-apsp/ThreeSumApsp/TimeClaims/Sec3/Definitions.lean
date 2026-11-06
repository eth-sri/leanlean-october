/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec3.Parameters
import ThreeSumApsp.Util.Asymptotics.UpperBounds

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
  /-- Negative Triangle, decision (`TriangleInstance.HasNegativeTriangle`).  Arguments `n u`. -/
  negativeTriangle : (ℕ → ℝ → ℝ) → Prop
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

/-- A larger bound on the running time is still a bound on the running time (for Exact Triangle). -/
def MonoExactTriangle (M : DetTimeModel) : Prop :=
  ∀ T T' : ℕ → ℝ → ℝ, (∀ (s : ℕ) (u : ℝ), 1 ≤ s → 1 ≤ u → T s u ≤ T' s u) →
    M.exactTriangle T → M.exactTriangle T'

/-- Two algorithms for Exact Triangle can be combined into one that looks at the number of vertices
and runs the first one below a fixed threshold `n₀` and the second one from the threshold on, at a
constant extra cost. -/
def ChooseBySize (M : DetTimeModel) : Prop :=
  ∀ n₀ : ℕ, ∃ C₀ : ℝ, ∀ T₁ T₂ : ℕ → ℝ → ℝ, M.exactTriangle T₁ → M.exactTriangle T₂ →
    M.exactTriangle fun n u => (if n < n₀ then T₁ n u else T₂ n u) + C₀

end Closure

namespace Claim

/-! ## Time sentences -/

/-- Proof of Theorem 19: "smaller instances are solved by brute force".  Trying all `n³`
triples; the factor `1 + log u` allows for weights that do not fit into one machine word. -/
def BruteForce (M : DetTimeModel) : Prop :=
  ∃ C : ℝ, M.exactTriangle fun n u => C * ((n : ℝ) ^ 3 * (1 + logU u))

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

/-- CITED.  After the proof of [CH20, Theorem 5.1]: from n integers bounded by a power of n, a
deterministic reduction computes polylogarithmically many arrays of length Õ(n), whose entries are
again bounded by a power of n, in Õ(n^{3/2}) time; three of the integers sum to 0 exactly if one of
the arrays is a yes-instance of Convolution-3SUM.  `E` is the extra time, `Num` the number of
instances, `N` their size, `mag` the bound on their numbers. -/
def CH20_Theorem_5_1 (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ (E Num mag : ℕ → ℝ) (N : ℕ → ℕ) (c' κ' : ℝ),
    IsPowPolylog E (3 / 2) ∧ IsPowPolylog Num 0 ∧ IsPowPolylog (fun n => (N n : ℝ)) 1 ∧
    (∀ n : ℕ, 1 ≤ n → 1 ≤ N n ∧ 1 ≤ mag n ∧ mag n ≤ c' * (n : ℝ) ^ κ') ∧
    ∀ T : ℕ → ℝ → ℝ, M.convolution3SUM T →
      ∃ T' : ℕ → ℝ → ℝ, M.threeSum T' ∧
        ∀ n : ℕ, 1 ≤ n → T' n ((n : ℝ) ^ κ) ≤ E n + Num n * T (N n) (mag n)

/-- CITED.  After the proof of [VW13, Theorem 4.3]: whether an array of `N` integers is a
yes-instance of Convolution-3SUM is decided by asking `O(√N)` times whether there is a zero
triangle, each time in an instance with `O(√N)` vertices in each part whose weights are entries of
the array, up to sign, or a filler, so that all weights are at most a constant times the bound on
the entries.

NOTE.  The time `E` of this reduction is part of the claim, because the time of Theorem 21(a) needs
`E(N) = N^{3/2+o(1)}`. -/
def VW13_Theorem_4_3 (M : DetTimeModel) : Prop :=
  ∃ (c : ℝ) (E Num : ℕ → ℝ) (size : ℕ → ℕ), 1 ≤ c ∧
    IsPowLittleO E (3 / 2) ∧ IsBigOPow Num (1 / 2) ∧ IsBigOPow (fun N => (size N : ℝ)) (1 / 2) ∧
    (∀ N : ℕ, 1 ≤ N → 1 ≤ size N) ∧
    ∀ T : ℕ → ℝ → ℝ, M.exactTriangle T →
      M.convolution3SUM fun N u => E N * (1 + logU u) + Num N * T (size N) (c * u)

/-- CITED.  [VW13, Theorem 3.3]: whether an instance with weights in `[−U, U]` has a negative
triangle is decided by asking `O(log U)` times whether there is a zero triangle, each time after
changing the weights, edge by edge, to numbers of absolute value `O(U)`; so a time `T(s)` for Exact
Triangle gives the time `O(T(s) log U)`.  (The constant is taken at least 2 so that the new running
time again satisfies `GoodTime`.) -/
def VW13_Theorem_3_3 (M : DetTimeModel) : Prop :=
  ∃ c C : ℝ, 1 ≤ c ∧ 2 ≤ C ∧ ∀ T : ℕ → ℝ → ℝ, GoodTime T → M.exactTriangle T →
    M.negativeTriangle fun s U => C * (T s (c * U) * logU U)

/-- CITED.  [VW18, Theorem 4.2]: from a running time for Negative Triangle that, divided by the
number of vertices, is nondecreasing (`GoodTime`), one gets a running time for the (min,+)-product
of two n × n matrices with entries in [−U, U], namely O(n² log U) times the time of Negative
Triangle on n^{1/3} vertices per part with weights O(U). -/
def VW18_Theorem_4_2 (M : DetTimeModel) : Prop :=
  ∃ c C : ℝ, 1 ≤ c ∧ 0 ≤ C ∧ ∀ T' : ℕ → ℝ → ℝ, GoodTime T' → M.negativeTriangle T' →
    ∃ T'' : ℕ → ℝ → ℝ, M.minPlusProduct T'' ∧
      ∀ (n : ℕ) (U : ℝ), 1 ≤ n → 1 ≤ U →
        T'' n U ≤ C * ((n : ℝ) ^ 2 * T' (cbrtCeil n) (c * U) * logU U)

/-! ## Claims that are derived from the ones above -/

/-- Exact Triangle is solved in time `K s^{3−δ} (log s + 1)^e (1 + log u)²` for ALL numbers `s ≥ 1`
of vertices per part and ALL bounds `u ≥ 1` on the weights.

NOTE.  This claim is not in the paper.  It is what our rendering of "Plug Theorem 19 into
Theorem 21" needs: Theorem 21(b) asks for a running time `T(s)`, with `T(s)/s` nondecreasing, at a
fixed bound on the weights and for all `s`, and Theorem 21(a) produces instances whose weights are
bounded in terms of `n`, not of their own size; Theorem 19 bounds the time only for weights at most
`s^κ` and for large `s`.  `exactTriangleUniform_of_explicit` derives it from
`Claim.Theorem_19_explicit`, brute force and the two closure properties; this works because the
bound in `Claim.Theorem_17` is polynomial in `κ` with a constant that does not depend on `κ`. -/
def ExactTriangleUniform (M : DetTimeModel) (δ : ℝ) (e : ℕ) : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ M.exactTriangle (uniformTime K δ e)

/-- **Theorem 21(a)**: "3SUM on n integers of absolute value at most n^ν reduces
deterministically, in n^{3/2+o(1)} time, to n^{1/2+o(1)} instances of Exact Triangle on n^{1/2+o(1)}
vertices per part with weights of absolute value n^{O(1)} [CH20, VW13]."  `E` is the time of the
reduction, `Num` the number of instances, `size` their number of vertices per part, `mag` the bound
on their weights. -/
def Theorem_21a (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ (E Num mag : ℕ → ℝ) (size : ℕ → ℕ) (c' κ' : ℝ),
    IsPowLittleO E (3 / 2) ∧ IsPowLittleO Num (1 / 2) ∧
    IsPowLittleO (fun n => (size n : ℝ)) (1 / 2) ∧
    (∀ n : ℕ, 1 ≤ n → 1 ≤ size n ∧ 1 ≤ mag n ∧ mag n ≤ c' * (n : ℝ) ^ κ') ∧
    ∀ T : ℕ → ℝ → ℝ, M.exactTriangle T →
      ∃ T' : ℕ → ℝ → ℝ, M.threeSum T' ∧
        ∀ n : ℕ, 1 ≤ n → T' n ((n : ℝ) ^ κ) ≤ E n + Num n * T (size n) (mag n)

/-- **Theorem 21(b)**, first half: "If a deterministic algorithm solves Exact
Triangle on s vertices per part with weights of absolute value at most cU, for a suitable constant
c, in time T(s) with T(s)/s nondecreasing, then the (min,+)-product of two n × n integer matrices
with entries of absolute value at most U can be computed deterministically in O(n² T(n^{1/3}) log²
U) time".  The paper's `T(s)` is `T s (c * U)`. -/
def Theorem_21b_minPlus (M : DetTimeModel) : Prop :=
  ∃ c C : ℝ, 1 ≤ c ∧ ∀ T : ℕ → ℝ → ℝ, GoodTime T → M.exactTriangle T →
    ∃ T' : ℕ → ℝ → ℝ, M.minPlusProduct T' ∧
      ∀ (n : ℕ) (U : ℝ), 1 ≤ n → 1 ≤ U →
        T' n U ≤ C * ((n : ℝ) ^ 2 * T (cbrtCeil n) (c * U) * logU U ^ 2)

/-- **Theorem 21(b)**, second half: "and APSP on directed n-vertex graphs with integer
weights of absolute value at most n^ν and no negative cycles in O(n² T(n^{1/3}) log³ n) time".

NOTE.  The printed hypothesis speaks of weights "at most cU" without saying what `U` is for APSP;
here it is `U = n^{κ+1}`, with `κ` for ν, which bounds the entries during the repeated squaring. -/
def Theorem_21b_apsp (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ c C : ℝ, 1 ≤ c ∧ ∀ T : ℕ → ℝ → ℝ, GoodTime T → M.exactTriangle T →
    ∃ T' : ℕ → ℝ → ℝ, M.apsp T' ∧
      ∀ n : ℕ, 2 ≤ n →
        T' n ((n : ℝ) ^ κ)
          ≤ C * ((n : ℝ) ^ 2 * T (cbrtCeil n) (c * (n : ℝ) ^ (κ + 1)) * Real.log n ^ 3)

/-! ## Bounds in `n` alone, along `u = n^κ` -/

/-- On numbers of absolute value at most `n^κ` the problem is solved deterministically in a time of
the class `Cls a`, for every constant `κ ≥ 0`.  Here `S` is the field of a `DetTimeModel` that
belongs to the problem, and `Cls` is `UpperBigOPow` for `O(n^a)`, `UpperPowPolylog` for
`O(n^a (log n)^{O(1)})` or `UpperPowLittleO` for `n^{a+o(1)}`. -/
def SolvedAlongPow (S : (ℕ → ℝ → ℝ) → Prop) (Cls : (ℕ → ℝ) → ℝ → Prop) (a : ℝ) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ T : ℕ → ℝ → ℝ, S T ∧ Cls (fun n => T n ((n : ℝ) ^ κ)) a

/-- 3SUM on `n` integers of absolute value at most `n^κ` is solved deterministically in
`n^{a+o(1)}` time, for every constant `κ ≥ 0`. -/
abbrev ThreeSumInLittleO (M : DetTimeModel) (a : ℝ) : Prop :=
  SolvedAlongPow M.threeSum UpperPowLittleO a

/-- The (min,+)-product of two `n × n` integer matrices with entries of absolute value at most `n^κ`
is computed deterministically in `O(n^a (log n)^{O(1)})` time, for every constant `κ ≥ 0`. -/
abbrev MinPlusInPolylog (M : DetTimeModel) (a : ℝ) : Prop :=
  SolvedAlongPow M.minPlusProduct UpperPowPolylog a

/-- APSP on directed `n`-vertex graphs with integer weights of absolute value at most `n^κ` and no
negative cycles is solved deterministically in `O(n^a (log n)^{O(1)})` time, for every constant
`κ ≥ 0`. -/
abbrev ApspInPolylog (M : DetTimeModel) (a : ℝ) : Prop :=
  SolvedAlongPow M.apsp UpperPowPolylog a
