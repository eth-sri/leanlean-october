/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ChoosePrime
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Loop
public import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.Chunks
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan

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
structure Et17Nums : Type where
  pD : ℕ
  pG : ℕ
  pSqrt : ℕ
  pScan : ℕ
  pChoose : ℕ
  pCap : ℕ
  pCeil : ℕ
  pBitLen : ℕ
  pDbl : ℕ
  pResid : ℕ
  pResidues : ℕ
  pClasses : ℕ
  pChunks : ℕ
  pS : ℕ
  pWriteX : ℕ
  pWriteY : ℕ
  ch : ChNums

namespace Et17

/- The locals of `et17`.  The arguments: `n`, `U`, the addresses of the three arrays of weights,
and the free pointer (the table of doubles is there).  Then `D`, `g`, `s = ⌊√D⌋`, the prime `p`,
`cap`, the number `q` of vertices of a piece, the number `h` of pieces, `len = bitLen U`, and `n²`.
Then the addresses of the residues of `w(a,b)`, `w(b,c)`, `w(a,c)`, of the starts of the classes,
the running places, the rows and the columns of the sorted pairs, the three components of the table
of chunks, `X`, `Y`, the answers, and the solver's free pointer.  Then `n² + p`, the number of
chunks, the number of instances, a flag (also the place for results that are not used), and `n D`.
-/
export ResidueTables (Size AdrAB AdrBC AdrAC Free ThePrime Bits SizeSq ResAB ResBC ResAC Small)
registers from 1 [Bound]
registers from 8 [ParD]
registers from 14 [Cls, ParG, RootD, Cap, PieceLen, NumPieces, Cur, Rows, Cols, TabR, TabL, TabW,
  MatX, MatY, AdrOut, SolverFree, Room, NumChunks, NumInst, Area]

end Et17

open Et17 in
/-- The first part of et17: `D`, `g`, `s`, and the flag that says whether `n` is small. -/
def et17Params (ν : Et17Nums) : Stmt :=
  .call ν.pD [v Size] ParD ;;
  .call ν.pG [v ParD] ParG ;;
  .call ν.pSqrt [v ParD] RootD ;;
  .ite (v ParD <' k 16) (.set Small (k 1)) (.set Small (v Small)) ;;
  .ite (v Size <' v ParD) (.set Small (k 1)) (.set Small (v Small)) ;;
  .ite (v ParG <' k 1) (.set Small (k 1)) (.set Small (v Small)) ;;
  .ite (v RootD <' v ParG) (.set Small (k 1)) (.set Small (v Small)) ;;
  .skip

open Et17 in
/-- The end of the second part: the sizes n², nD, n² + p, and the addresses of the arrays. -/
def et17Addr : Stmt :=
  ResidueTables.addresses Cls ;;
  .set Area (v Size *' v ParD) ;;
  .set Room (v SizeSq +' v ThePrime) ;;
  .set Cur (v Cls +' (v ThePrime +' k 1)) ;;
  .set Rows (v Cur +' v ThePrime) ;;
  .set Cols (v Rows +' v SizeSq) ;;
  .set TabR (v Cols +' v SizeSq) ;;
  .set TabL (v TabR +' v Room) ;;
  .set TabW (v TabL +' v Room) ;;
  .set MatX (v TabW +' v Room) ;;
  .set MatY (v MatX +' v Area) ;;
  .set AdrOut (v MatY +' v Area) ;;
  .set SolverFree (v AdrOut +' v Cap) ;;
  .skip

open Et17 in
/-- Choose the prime, compute the sizes, set `ParD` to the middle dimension, and lay out the arrays. -/
def et17Sizes (ν : Et17Nums) : Stmt :=
  .call ν.pChoose [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v ParD, v Free] ThePrime ;;
  .call ν.pCap [v Size, v ParD] Cap ;;
  .call ν.pCeil [v RootD, v ParG] PieceLen ;;
  .call ν.pCeil [v Size, v PieceLen] NumPieces ;;
  .call ν.pBitLen [v Bound] Bits ;;
  .set ParD (v PieceLen *' v RootD) ;;
  et17Addr

/-! ## Time and need

The additive constants in the time functions are upper bounds for the cost of evaluating arguments,
of calls and of tests.  They are not meant to be tight. -/

/-- n is small for the parameters D and g: the host runs the brute force. -/
def SmallCase (n D g : ℕ) : Prop := D < 16 ∨ n < D ∨ g < 1 ∨ Nat.sqrt D < g

instance (n D g : ℕ) : Decidable (SmallCase n D g) := by unfold SmallCase; infer_instance

/-- The largest time of the solver on an instance with at most cap query pairs. -/
def supTime (Tn : List ℕ → ℕ) (n D cap : ℕ) : ℕ :=
  (Finset.range (cap + 1)).sup fun w => Tn [n, D, w]

/-- The largest need of the solver on an instance with at most cap query pairs. -/
def supNeed (need : List ℕ → Need) (n D cap : ℕ) : Need :=
  ⟨(Finset.range (cap + 1)).sup fun w => (need [n, D, w]).word,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).cells,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).depth⟩

/-- Proof of Theorem 17: "F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)" for the selected prime.
Here the second form, with the constant `Hashing.falsePositiveConst` and with κ = kappaOf n U =
max(1, log U / log n), so that U ≤ n^κ. -/
noncomputable def falsePositiveBound (n U D : ℕ) : ℕ :=
  ⌊Hashing.falsePositiveConst * (kappaOf n U * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D)⌋₊

/-- The time of the parameter procedures, of the square root and of the tests. -/
def hostSetup (tD tG : ℕ → ℕ) (n D : ℕ) : ℕ := tD n + tG D + (18 * Nat.sqrt D + 12) + 60

/-- The cells of the arrays of et17, with s in place of the prime. -/
def hostLayout (n U D : ℕ) : ℕ :=
  (bitLen U + 1) + 3 * (n * n) + (Nat.sqrt D + 1) + Nat.sqrt D + 2 * (n * n)
    + 3 * (n * n + Nat.sqrt D) + 2 * (n * D) + queryCapNat n D

/-- The largest number that et17 and the procedures below it form, apart from the solver; a and b
bound the numbers that the two parameter procedures form. -/
def hostWord (a b n U D g : ℕ) : ℕ :=
  a + b                                                     -- the two parameter procedures
    + (4 * D + 4)                                           -- the square root, the primes up to √D
    + (3 * U + 1)                                           -- a sum of three weights
    + (2 * U + 2)                                           -- the number of binary digits of U
    + (2 * n + 1)                                           -- the power of two above n
    + Nat.sqrt D * 2 ^ (bitLen U + 1)                       -- the table of doubles
    + 4 * (32 ^ Nat.clog 2 n * Nat.sqrt D)                  -- the entries in Strassen's algorithm
    + n * n * (32 ^ Nat.clog 2 n * Nat.sqrt D)              -- the count for a prime
    + (4 * n ^ 4 + D + 2)                                   -- cap
    + (Nat.sqrt D + g + 1)                                  -- the size of a piece
    + (n + pieceSizeNat D g + 1)                                -- the number of pieces
    + 4 * n * g                                             -- the number of instances
    + 100

/-- The inner dimension that the variant host hands to the solver: `⌈⌊√D⌋/g⌉ ⌊√D⌋`, the number of
vertices of a piece times the largest possible prime. -/
def midSize (D g : ℕ) : ℕ := pieceSizeNat D g * Nat.sqrt D

/-- A piece has at most `⌊√D⌋` vertices, for every `g`. -/
theorem pieceSizeNat_le_sqrt (D g : ℕ) : pieceSizeNat D g ≤ Nat.sqrt D := by
  unfold pieceSizeNat
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  · exact (ceilDiv_le_iff_le_smul hg).2 (by simpa using Nat.le_mul_of_pos_left _ hg)

/-- The inner dimension of the variant is at most `D`, for every `g`. -/
theorem midSize_le (D g : ℕ) : midSize D g ≤ D :=
  (Nat.mul_le_mul_right _ (pieceSizeNat_le_sqrt D g)).trans (Nat.sqrt_le D)

/-- The inner dimension of the variant is positive under the hypotheses of Theorem 17. -/
theorem one_le_midSize {D g : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g) : 1 ≤ midSize D g := by
  have hsqrt : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  have hpiece : 1 ≤ pieceSizeNat D g := (Nat.lt_ceilDiv_iff hg).2 (by omega)
  exact Nat.mul_pos hpiece (by omega)

/-- The host uses `n²` cells for the flags and calls its solver at `midSize D g`. -/
def hostNeedAt (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) : Need :=
  ⟨hostWord a b n U D g + (supNeed need n (midSize D g) (queryCapNat n D)).word,
    chooseCells n U D + hostLayout n U D + (supNeed need n (midSize D g) (queryCapNat n D)).cells + 2 + n * n,
    2 * Nat.clog 2 n + 8 + (supNeed need n (midSize D g) (queryCapNat n D)).depth⟩

/-- **The need of the host**, over a solver with the need `need`; wD and wG bound the numbers that
the parameter procedures form. -/
def hostNeed (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ)
    (levels : ℕ := 0) : Need :=
  let r := hostNeedAt (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))
  { r with depth := r.depth + levels }

/-! ## The context -/

/-- A procedure that computes a function of one number and changes no cell; t is its time, w bounds
the numbers it forms, and it nests calls at most three deep. -/
def ParamProc (P : Program) (p : ℕ) (f t w : ℕ → ℕ) : Prop :=
  ∀ (lim : Limits) (d x : ℕ) (μ : ℕ → ℤ), 1 ≤ x → (lim.space : ℤ) ≤ lim.word →
    ((w x : ℕ) : ℤ) ≤ lim.word → d + 4 ≤ lim.depth →
    Meets lim P p (d + 1) [(x : ℤ)] μ (t x) fun r μ' => r = (f x : ℕ) ∧ μ' = μ

/-- The context of et17: the solver and what hostLoop calls; the procedures of the host; the
two parameter procedures. -/
structure Et17Ctx (P₀ R : Program) (ν : Et17Nums) (Tn : List ℕ → ℕ) (need : List ℕ → Need)
    (Dfun Gfun tD tG wD wG : ℕ → ℕ) : Prop where
  loop : HostCtx P₀ R ν.pS ν.pWriteX ν.pWriteY ν.pScan Tn need
  hSqrt : (P₀ ++ R)[ν.pSqrt]? = some sqrtBody
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
  ⟨x.n, midSize D g, chosenPrime x.n D x.AB x.BC x.AC, pieceSizeNat D g, queryCapNat x.n D, x.AB,
    x.BC, x.AC⟩

def aRab (_X : HostData) (U fr : ℕ) : ℕ := fr + (bitLen U + 1)
/-- The address of the residues of `w(b,c)`. -/
def aRbc (X : HostData) (U fr : ℕ) : ℕ := ResidueTables.rbc fr (bitLen U) X.n
/-- The address of the residues of `w(a,c)`. -/
def aRac (X : HostData) (U fr : ℕ) : ℕ := ResidueTables.rac fr (bitLen U) X.n
/-- The address of the starts of the classes. -/
def aCls (X : HostData) (U fr : ℕ) : ℕ := ResidueTables.top fr (bitLen U) X.n
/-- The address of the running places. -/
def aCur (X : HostData) (U fr : ℕ) : ℕ := aCls X U fr + (X.p + 1)
/-- The address of the rows of the sorted pairs. -/
def aQi (X : HostData) (U fr : ℕ) : ℕ := aCur X U fr + X.p
/-- The address of the columns of the sorted pairs. -/
def aQj (X : HostData) (U fr : ℕ) : ℕ := aQi X U fr + X.n * X.n
/-- The address of the residues of the chunks. -/
def aCr (X : HostData) (U fr : ℕ) : ℕ := aQj X U fr + X.n * X.n
/-- The address of the starts of the chunks. -/
def aCl (X : HostData) (U fr : ℕ) : ℕ := aCr X U fr + (X.n * X.n + X.p)
/-- The address of the lengths of the chunks. -/
def aCw (X : HostData) (U fr : ℕ) : ℕ := aCl X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matX` of an instance. -/
def aX (X : HostData) (U fr : ℕ) : ℕ := aCw X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matY` of an instance. -/
def aY (X : HostData) (U fr : ℕ) : ℕ := aX X U fr + X.n * X.D
/-- The address of the answers. -/
def aOut (X : HostData) (U fr : ℕ) : ℕ := aY X U fr + X.n * X.D
/-- The free pointer that is handed to the solver. -/
def aFr (X : HostData) (U fr : ℕ) : ℕ := aOut X U fr + X.cap

/-- The arrays of the host stand one after the other. -/
theorem host_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCur X U fr = aCls X U fr + (X.p + 1) ∧ aQi X U fr = aCur X U fr + X.p ∧
      aQj X U fr = aQi X U fr + X.n * X.n ∧ aCr X U fr = aQj X U fr + X.n * X.n ∧
      aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧ aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧
      aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧ aY X U fr = aX X U fr + X.n * X.D ∧
      aOut X U fr = aY X U fr + X.n * X.D ∧ aFr X U fr = aOut X U fr + X.cap :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The addresses that hostLoop gets. -/
def hostAddr (x : TriInst) (X : HostData) (fr : ℕ) : HostAddr :=
  ⟨x.ab, x.bc, x.ac, aRac X x.U fr, aRbc X x.U fr, aQi X x.U fr, aQj X x.U fr, aCr X x.U fr,
    aCl X x.U fr, aCw X x.U fr, aX X x.U fr, aY X x.U fr, aOut X x.U fr, aFr X x.U fr + X.n * X.n⟩

/-- The locals at the start: the arguments, then zeros. -/
def et17Loc0 (x : TriInst) (fr : ℕ) : List ℤ :=
  ([x.n, x.U, x.ab, x.bc, x.ac, fr] : List ℤ) ++ List.replicate 28 0

/-- The locals after the first part. -/
def et17LocA (x : TriInst) (fr D g : ℕ) : List ℤ :=
  [(x.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), 0, 0, (D : ℤ), 0, 0, 0,
    0, (if SmallCase x.n D g then 1 else 0), 0, (g : ℤ), ((Nat.sqrt D : ℕ) : ℤ), 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The locals of the third part, for the data X of the loop: those after the second part, with the
number of chunks in NumChunks and the result of the last call in Small.  ParG and RootD are not
read. -/
abbrev Et17.suffix (x : TriInst) (X : HostData) (fr : ℕ) (g s nch : ℤ) : List ℤ :=
  [((aCls X x.U fr : ℕ) : ℤ), g, s, (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ),
    ((aCur X x.U fr : ℕ) : ℤ), ((aQi X x.U fr : ℕ) : ℤ), ((aQj X x.U fr : ℕ) : ℤ),
    ((aCr X x.U fr : ℕ) : ℤ), ((aCl X x.U fr : ℕ) : ℤ), ((aCw X x.U fr : ℕ) : ℤ),
    ((aX X x.U fr : ℕ) : ℤ), ((aY X x.U fr : ℕ) : ℤ), ((aOut X x.U fr : ℕ) : ℤ),
    ((aFr X x.U fr : ℕ) : ℤ), ((X.n * X.n + X.p : ℕ) : ℤ), nch, 0, ((X.n * X.D : ℕ) : ℤ)]

abbrev Et17.locals (x : TriInst) (X : HostData) (fr : ℕ) (g s nch res : ℤ) : List ℤ :=
  ResidueTables.locals X.n x.ab x.bc x.ac fr X.p (bitLen x.U) x.U X.D res ++ Et17.suffix x X fr g s nch

/-- The locals after the second part of the variant (n is not small, so the flag is 0). -/
def et17LocB (x : TriInst) (fr D g : ℕ) : List ℤ :=
  Et17.locals x (hostData x D g) fr g (Nat.sqrt D : ℕ) 0 0

end Light.Sec3
