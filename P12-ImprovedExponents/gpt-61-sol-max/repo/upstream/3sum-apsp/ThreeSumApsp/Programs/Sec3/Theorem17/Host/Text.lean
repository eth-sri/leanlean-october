/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ChoosePrime
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Loop
public import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.Chunks
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.BruteForce

/-!
# The host of Theorem 17: the top procedure

The host procedure et17(n, U, ab, bc, ac, fr) decides Exact Triangle with the help of an arbitrary
solver of Lop-AE-SparseTri (proof of Theorem 17).  It computes the parameters `D` and `g` by two
procedures that are parameters of the construction, and `s = ⌊√D⌋`.  For small `n`
(`D < 16`, `n < D`, `g < 1` or `s < g`) it runs the brute force.  Otherwise it chooses the prime,
computes the largest number of query pairs, the number of vertices of a piece and the number of
pieces, lays out its arrays from the free pointer on, computes the residues of the weights, sorts
the pairs `(a, b)` into classes, cuts the classes into chunks, and runs the loop over the instances.

This file holds the program (`et17Body`), its time and its need (`hostTime`, `hostNeed`), what it
assumes about the program around it (`Et17Ctx`), and the data, the addresses and the local variables
of a run.

**The way through the files on the host**, each named by its main result.

1. The instances as data, with no program in sight: what the host writes, what the solver answers
   and which scans succeed (`HostData`); a zero triangle is found if and only if there is one
   (`HostData.found_m`); a failed scan belongs to a false positive of its own
   (`HostData.sum_fails_le`); there are at most 4ng instances (`HostData.m_le`).
2. The loop over the instances (`hostLoop_spec`).
3. The text of the top procedure (this file), in three parts and the small case.
4. The parts: the parameters and the small case (`et17Params_spec`, `et17Small_spec`); the prime,
   the sizes and the addresses (`et17Sizes_spec`, `et17Addr_spec`); the arrays and the call of the
   loop (`et17Tables_spec`).
5. What the parts need: the limits cover what the called procedures ask for (`choosePre_of_ok`,
   `hostLim_of_ok`), and the time of a run is within the worst case (`hostRunTime_le`).
6. The parts together: et17 decides Exact Triangle (`et17_spec`).
7. The list of the procedures with their numbers; with a solver it is a solver (`et17Procs`,
   `et17_solves`).
8. For the claim: the need is polynomially bounded (`hostNeed_poly`), the time obeys the bound of
   Theorem 17 (`obeysBound17_hostTime`), and so the claim holds for programs of the light language
   (`claim17_of_host`, `claim_theorem_17₅`, `claim_theorem_17₂₆`).

The layout, from the free pointer `fr` on: the table of doubles (`len + 1` cells, where
`len = bitLen U` is the number of binary digits of `U`; cell `j` holds `2^j p`, for residues without
division); the residues of `w(a,b)`, `w(b,c)`, `w(a,c)` (`n²` each); the starts of the classes
(`p + 1`); running places (`p`; while the pairs are sorted, cell `ϱ` holds the next free place of
the class `ϱ`); rows and columns of the sorted pairs (`n²` each); the three components of the table
of chunks (`n² + p` each); `X` (`n D`); `Y` (`D n`); the answers (`cap`); the solver's free pointer.

Notation: `κ` is the exponent in `|w(e)| ≤ n^κ`, the paper's ν; as in the paper, `F(p)` is the
number of false positives of `p`, that is, of triples with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≠ 0`
and `p ∣ S(a,b,c)`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The procedure -/

/-- The numbers of the procedures that et17 calls, directly or through the procedures that it
calls: the two parameter procedures, sqrt, brute, scan, choosePrime, queryCapNat, ceilDiv, bitLen,
dblTable, resid, residues, classes, chunks, hostLoop, the solver, writeX, writeY, scanPairs, and
the procedures below choosePrime. -/
structure Et17Nums where
  (pD pG pSqrt pBrute pScan pChoose pCap pCeil pBitLen pDbl pResid pResidues pClasses pChunks pLoop pS pWriteX pWriteY pScanPairs : ℕ)
  ch : ChNums


/-- The first part of et17: `D`, `g`, `s`, and the flag that says whether `n` is small. -/
def et17Params (ν : Et17Nums)  :=
  .call ν.pD [v 0] 6 ;;
  .call ν.pG [v 6] 7 ;;
  .call ν.pSqrt [v 6] 8 ;;
  .ite (v 6 <' k 16) (.set 33 (k 1)) (.set 33 (v 33)) ;;
  .ite (v 0 <' v 6) (.set 33 (k 1)) (.set 33 (v 33)) ;;
  .ite (v 7 <' k 1) (.set 33 (k 1)) (.set 33 (v 33)) ;;
  .ite (v 8 <' v 7) (.set 33 (k 1)) (.set 33 (v 33)) ;;
  .skip

/-- The end of the second part: the sizes n², nD, n² + p, and the addresses of the arrays. -/
def et17Addr  :=
  .set 14 (v 0 *' v 0) ;;
  .set 34 (v 0 *' v 6) ;;
  .set 30 (v 14 +' v 9) ;;
  .set 16 (v 5 +' (v 13 +' k 1)) ;;
  .set 17 (v 16 +' v 14) ;;
  .set 18 (v 17 +' v 14) ;;
  .set 19 (v 18 +' v 14) ;;
  .set 20 (v 19 +' (v 9 +' k 1)) ;;
  .set 21 (v 20 +' v 9) ;;
  .set 22 (v 21 +' v 14) ;;
  .set 23 (v 22 +' v 14) ;;
  .set 24 (v 23 +' v 30) ;;
  .set 25 (v 24 +' v 30) ;;
  .set 26 (v 25 +' v 30) ;;
  .set 27 (v 26 +' v 34) ;;
  .set 28 (v 27 +' v 34) ;;
  .set 29 (v 28 +' v 10) ;;
  .skip

/-- The third part: the residues, the classes, the chunks, and the loop over the instances. -/
def et17TablesWith (ν : Et17Nums) (pLoop : ℕ) (fr : Expr)  :=
  .call ν.pDbl [v 5, v 9, v 13] 33 ;;
  .call ν.pResidues [v 2, v 16, v 14, v 5, v 13] 33 ;;
  .call ν.pResidues [v 3, v 17, v 14, v 5, v 13] 33 ;;
  .call ν.pResidues [v 4, v 18, v 14, v 5, v 13] 33 ;;
  .call ν.pClasses [v 16, v 0, v 9, v 19, v 20, v 21, v 22] 33 ;;
  .call ν.pChunks [v 19, v 9, v 10, v 23, v 24, v 25] 31 ;;
  .set 32 (v 12 *' v 31) ;;
  .call pLoop [v 0, v 6, v 9, v 11, v 31, v 32, v 2, v 3,
    v 4, v 18, v 17, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28,
    fr] 0

def et17Tables ν := et17TablesWith ν ν.pLoop (v 29)

/-! ## Time and need

The additive constants in the time functions are upper bounds for the cost of evaluating arguments,
of calls and of tests.  They are not meant to be tight. -/

/-- n is small for the parameters D and g: the host runs the brute force. -/
def SmallCase n D g := D < 16 ∨ n < D ∨ g < 1 ∨ Nat.sqrt D < g

instance (n D g : ℕ) : Decidable (SmallCase n D g) := by unfold SmallCase; infer_instance

/-- The largest time of the solver on an instance with at most cap query pairs. -/
def supTime (Tn : Light.InputTime) n D cap :=
  (Finset.range (cap + 1)).sup fun w => Tn [n, D, w]

/-- The largest need of the solver on an instance with at most cap query pairs. -/
def supNeed (need : Light.InputNeed) (n D cap : ℕ) : Need :=
  ⟨(Finset.range (cap + 1)).sup fun w => (need [n, D, w]).word,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).cells,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).depth⟩

/-- Proof of Theorem 17: "F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)" for the selected prime.
Here the second form, with the constant `Hashing.falsePositiveConst` and with κ = kappaOf n U =
max(1, log U / log n), so that U ≤ n^κ. -/
noncomputable def falsePositiveBound (n U D : ℕ) :=
  ⌊Hashing.falsePositiveConst * (kappaOf n U * n ^ 3 * Real.log n / Real.sqrt D)⌋₊

/-- The time of the parameter procedures, of the square root and of the tests. -/
def hostSetup (tD tG : ℕ → ℕ) n D := tD n + tG D + (18 * Nat.sqrt D + 12) + 60

/-- A bound on the time of the loop over the instances: at most 4ng instances, with pieces of at
most q vertices and at most cap query pairs, and at most falsePositiveBound + 1 scans. -/
noncomputable def hostLoopBound Tn n U D g :=
  4 * n * g *
      (tWrites n D (pieceSizeNat D g) + supTime Tn n D (queryCapNat n D)
        + tAnswers (queryCapNat n D))
    + tScanCall (pieceSizeNat D g) * (falsePositiveBound n U D + 1) + 14

/-- The time of et17 after the tests, if n is not small. -/
noncomputable def hostMain Tn n U D g :=
  chooseTime n U D + tQueryCapNat n D + tCeilDiv (Nat.sqrt D) g + tCeilDiv n (pieceSizeNat D g)
    + tBitLen U + tDblTable (bitLen U) + 3 * tResidues (n * n) (bitLen U) + tClasses n (Nat.sqrt D)
    + tChunks (Nat.sqrt D) (4 * n * g) + hostLoopBound Tn n U D g + 300

/-- **A bound on the time of the host in the worst case**, for the parameter functions Dfun, Gfun
with the times tD, tG, over a solver with the time Tn. -/
noncomputable def hostTime (Dfun Gfun tD tG : ℕ → ℕ) Tn n U :=
  hostSetup tD tG n (Dfun n) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then tBrute n + 20
    else hostMain Tn n U (Dfun n) (Gfun (Dfun n))

/-- The cells of the arrays of et17, with s in place of the prime. -/
def hostLayout n U D :=
  bitLen U + 1 + 3 * (n * n) + Nat.sqrt D + 1 + Nat.sqrt D + 2 * (n * n)
    + 3 * (n * n + Nat.sqrt D) + 2 * (n * D) + queryCapNat n D

/-- The largest number that et17 and the procedures below it form, apart from the solver; a and b
bound the numbers that the two parameter procedures form. -/
def hostWord a b n U D g :=
  a + b                                                     -- the two parameter procedures
    + 4 * D + 4                                           -- the square root, the primes up to √D
    + 3 * U + 1                                           -- a sum of three weights
    + 2 * U + 2                                           -- the number of binary digits of U
    + 2 * n + 1                                           -- the power of two above n
    + Nat.sqrt D * 2 ^ (bitLen U + 1)                       -- the table of doubles
    + 4 * (16 ^ Nat.clog 2 n * Nat.sqrt D)                  -- the entries in Strassen's algorithm
    + n * n * (16 ^ Nat.clog 2 n * Nat.sqrt D)              -- the count for a prime
    + (4 * n ^ 4 + D + 2)                                   -- cap
    + (Nat.sqrt D + g + 1)                                  -- the size of a piece
    + (n + pieceSizeNat D g + 1)                                -- the number of pieces
    + 4 * n * g                                             -- the number of instances
    + 100

/-- The need of the host for given parameters D and g. -/
def hostNeedAt (a b : ℕ) (need : Light.InputNeed) (n U D g : ℕ) : Need :=
  ⟨hostWord a b n U D g + (supNeed need n D (queryCapNat n D)).word,
    chooseCells n U D + hostLayout n U D + (supNeed need n D (queryCapNat n D)).cells + 2,
    2 * Nat.clog 2 n + 8 + (supNeed need n D (queryCapNat n D)).depth⟩

/-- **The need of the host**, over a solver with the need `need`; wD and wG bound the numbers that
the parameter procedures form. -/
def hostNeed (Dfun Gfun wD wG : ℕ → ℕ) need n U :=
  hostNeedAt (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))

/-! ## The context -/

/-- A procedure that computes a function of one number and changes no cell; t is its time, w bounds
the numbers it forms, and it nests calls at most three deep. -/
def ParamProc P p (f t w : ℕ → ℕ) :=
  ∀ (lim : Limits) (d x : ℕ) (μ : Light.Memory), 1 ≤ x → (lim.space : ℤ) ≤ lim.word →
    (w x : ℤ) ≤ lim.word → d + 4 ≤ lim.depth →
    Meets lim P p (d + 1) [x] μ (t x) fun r μ' => r = f x ∧ μ' = μ

/-- A parameter routine remains valid behind any prefix and before any suffix. -/
abbrev ParamFamily (procs : ℕ → Program) (i : ℕ) (f t w : ℕ → ℕ) :=
  ∀ Q R, ParamProc (Q ++ procs Q.length ++ R) (Q.length + i) f t w

/-- The context of et17: the solver and what hostLoop calls; the procedures of the host; the
two parameter procedures. -/
structure Et17Ctx (P₀ R : Program) (ν : Et17Nums) (Tn : Light.InputTime) (need : Light.InputNeed)
    (Dfun Gfun tD tG wD wG : ℕ → ℕ) : Prop where
  loop : HostCtx P₀ R ν.pS ν.pWriteX ν.pWriteY ν.pScanPairs ν.pScan Tn need
  hLoop : (P₀ ++ R)[ν.pLoop]? = some (hostLoopBody ν.pS ν.pWriteX ν.pWriteY ν.pScanPairs)
  hSqrt : (P₀ ++ R)[ν.pSqrt]? = some sqrtBody
  hBrute : (P₀ ++ R)[ν.pBrute]? = some (bruteBody ν.pScan)
  hChoose : (P₀ ++ R)[ν.pChoose]? = some (choosePrimeBody ν.ch)
  ch : ChCtx (P₀ ++ R) ν.ch
  hCap : (P₀ ++ R)[ν.pCap]? = some queryCapNatBody
  hCeil : (P₀ ++ R)[ν.pCeil]? = some ceilDivBody
  hBitLen : (P₀ ++ R)[ν.pBitLen]? = some bitLenBody
  hDbl : (P₀ ++ R)[ν.pDbl]? = some dblTableBody
  hResid : (P₀ ++ R)[ν.pResid]? = some residBody
  hResidues : (P₀ ++ R)[ν.pResidues]? = some (residuesBody ν.pResid)
  hClasses : (P₀ ++ R)[ν.pClasses]? = some classesBody
  hChunks : (P₀ ++ R)[ν.pChunks]? = some chunksBody
  dProc : ParamProc (P₀ ++ R) ν.pD Dfun tD wD
  gProc : ParamProc (P₀ ++ R) ν.pG Gfun tG wG
  D_pos : ∀ n, 1 ≤ n → 1 ≤ Dfun n

/-! ## The data, the addresses and the local variables of a run -/

/-- The data of the loop over the instances, for the parameters D and g. -/
def hostData (x : TriInst) (D g : ℕ) : HostData :=
  ⟨x.n, D, chosenPrime x.n D x.AB x.BC x.AC, pieceSizeNat D g, queryCapNat x.n D, x.AB, x.BC, x.AC⟩

/-- The address of the residues of `w(a,b)`; the table of doubles is at fr. -/
def aRab (_X : HostData) U fr := fr + bitLen U + 1
/-- The address of the residues of `w(b,c)`. -/
def aRbc X U fr := aRab X U fr + X.n * X.n
/-- The address of the residues of `w(a,c)`. -/
def aRac X U fr := aRbc X U fr + X.n * X.n
/-- The address of the starts of the classes. -/
def aCls X U fr := aRac X U fr + X.n * X.n
/-- The address of the running places. -/
def aCur X U fr := aCls X U fr + X.p + 1
/-- The address of the rows of the sorted pairs. -/
def aQi X U fr := aCur X U fr + X.p
/-- The address of the columns of the sorted pairs. -/
def aQj X U fr := aQi X U fr + X.n * X.n
/-- The address of the residues of the chunks. -/
def aCr X U fr := aQj X U fr + X.n * X.n
/-- The address of the starts of the chunks. -/
def aCl X U fr := aCr X U fr + (X.n * X.n + X.p)
/-- The address of the lengths of the chunks. -/
def aCw X U fr := aCl X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matX` of an instance. -/
def aX X U fr := aCw X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matY` of an instance. -/
def aY X U fr := aX X U fr + X.n * X.D
/-- The address of the answers. -/
def aOut X U fr := aY X U fr + X.n * X.D
/-- The free pointer that is handed to the solver. -/
def aFr X U fr := aOut X U fr + X.cap

/-- The arrays of the host stand one after the other. -/
theorem host_places X U fr :
    aRab X U fr = fr + bitLen U + 1 ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCur X U fr = aCls X U fr + X.p + 1 ∧ aQi X U fr = aCur X U fr + X.p ∧
      aQj X U fr = aQi X U fr + X.n * X.n ∧ aCr X U fr = aQj X U fr + X.n * X.n ∧
      aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧ aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧
      aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧ aY X U fr = aX X U fr + X.n * X.D ∧
      aOut X U fr = aY X U fr + X.n * X.D ∧ aFr X U fr = aOut X U fr + X.cap :=
  by (repeat' constructor)

/-- The addresses that hostLoop gets. -/
def hostAddr (x : TriInst) (X : HostData) (fr : ℕ) : HostAddr :=
  ⟨x.ab, x.bc, x.ac, aRac X x.U fr, aRbc X x.U fr, aQi X x.U fr, aQj X x.U fr, aCr X x.U fr,
    aCl X x.U fr, aCw X x.U fr, aX X x.U fr, aY X x.U fr, aOut X x.U fr, aFr X x.U fr⟩

/-- The locals at the start: the arguments, then zeros. -/
def et17Loc0 (x : TriInst) (fr : ℕ)  :=
  [(x.n : ℤ), x.U, x.ab, x.bc, (x.ac : ℤ), (fr : ℤ)] ++ List.replicate 29 (0 : ℤ)

/-- The locals after the first part. -/
def et17LocA (x : TriInst) (fr D g : ℕ) : List ℤ :=
  [(x.n : ℤ), x.U, x.ab, x.bc, (x.ac : ℤ), (fr : ℤ), (D : ℤ), (g : ℤ), (Nat.sqrt D : ℤ)] ++ List.replicate 24 (0 : ℤ) ++ [if SmallCase x.n D g then 1 else 0, 0]

/-- The locals of the third part, for the data X of the loop: those after the second part, with the
number of chunks in NumChunks and the result of the last call in Small.  ParG and RootD are not
read. -/
abbrev Et17.locals (x : TriInst) (X : HostData) (fr : ℕ) (g s nch res : ℤ) : List ℤ :=
  [X.n, x.U, x.ab, x.bc, (x.ac : ℤ), (fr : ℤ), (X.D : ℤ), g, s, (X.p : ℤ),
    (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ), (bitLen x.U : ℤ), ((X.n * X.n : ℕ) : ℤ), 0,
    (aRab X x.U fr : ℤ), (aRbc X x.U fr : ℤ), (aRac X x.U fr : ℤ),
    (aCls X x.U fr : ℤ), (aCur X x.U fr : ℤ), (aQi X x.U fr : ℤ),
    (aQj X x.U fr : ℤ), (aCr X x.U fr : ℤ), (aCl X x.U fr : ℤ),
    (aCw X x.U fr : ℤ), (aX X x.U fr : ℤ), (aY X x.U fr : ℤ),
    (aOut X x.U fr : ℤ), (aFr X x.U fr : ℤ), ((X.n * X.n + X.p : ℕ) : ℤ), nch, 0, res,
    ((X.n * X.D : ℕ) : ℤ)]

/-- The time of the third part in a run: it depends on the data. -/
def hostRunTime Tn X U :=
  tDblTable (bitLen U) + 3 * tResidues (X.n * X.n) (bitLen U) + tClasses X.n X.p
    + tChunks X.p X.chunkCount + tHostLoop Tn X + 80

end Light.Sec3
