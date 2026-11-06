module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.Strassen
public import ThreeSumApsp.Lang.Lib.NextPair
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ZOrder
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Strassen
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Residues

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The steps and the scratch space of Strassen's recursion

At level j the operands are 2^j × 2^j matrices whose entries are vectors of p numbers, so that an
operand has 4^j · p numbers.  strScr p j ≤ 4^j · p (`strScr_le`), and both strScr and strSteps are
monotone in p.
-/


namespace Light.Sec3

/-- The scratch space, exactly. -/
theorem strScr_add (p j : ℕ) : strScr p j + p = 4 ^ j * p := by
  induction j with
  | zero => simp [strScr]
  | succ j ih =>
    rw [strScr, pow_succ]
    have : 4 ^ j * 4 * p = 4 * (4 ^ j * p) := by ring
    omega

/-- The scratch space is at most the size of an operand. -/
theorem strScr_le (p j : ℕ) : strScr p j ≤ 4 ^ j * p := by
  have := strScr_add p j
  omega

/-- The scratch space grows with p. -/
theorem strScr_mono {p q : ℕ} (h : p ≤ q) (j : ℕ) : strScr p j ≤ strScr q j := by
  induction j with
  | zero => simp [strScr]
  | succ j ih =>
    rw [strScr, strScr]
    have := Nat.mul_le_mul_left (4 ^ j) h
    omega

/-- The number of steps grows with p. -/
theorem strSteps_mono {p q : ℕ} (h : p ≤ q) (j : ℕ) : strSteps p j ≤ strSteps q j := by
  induction j with
  | zero =>
    rw [strSteps, strSteps]
    have h2 : p * p ≤ q * q := Nat.mul_le_mul h h
    have e1 : 32 * p * p = 32 * (p * p) := by ring
    have e2 : 32 * q * q = 32 * (q * q) := by ring
    omega
  | succ j ih =>
    rw [strSteps, strSteps]
    have := Nat.mul_le_mul_left (4 ^ j) h
    omega


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The count of the proof of Theorem 17, read off the product PQ

"then F(p) + Z₀ is the sum over the pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in
(PQ)[a,b]."  Here F(p) is the number of false positives of p, that is, of triples with S(a,b,c) =
w(a,b) + w(b,c) + w(a,c) ≠ 0 and p ∣ S(a,b,c), and Z₀ is the number of zero triangles.

This file proves that the routine countZero returns this sum, `countBy`.  It does not prove that the
sum is F(p) + Z₀: that is `countOf_eq`, a theorem about lists with no program in it.

countZero(rm, rab, mort, n, p): the cells from rm hold the product PQ, a matrix of 4^K vectors of p
coefficients each, in Z-order, where 2^K ≥ n; the cells from rab hold the residues of the weights
w(a,b) mod p, that of (a, b) at place a n + b; the cells from mort hold the table of `spread`, from
which the place of a pair in Z-order is formed.  The routine goes through the pairs (a, b) in the
order of their places a n + b, reads the residue ϱ of w(a,b), forms (p - ϱ) mod p by one test, and
adds the coefficient number (p - ϱ) mod p of the vector of (a, b) (`countTerm`,
`countZeroAdd_spec`); then it steps to the next pair.  The loop is `countZero_spec`.
-/



open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace CountZero

/-- The local variables of countZero.  The arguments: Mat = rm, Residues = rab, Places = mort,
Num = n, Prime = p.  Then Square = n²; Idx = t = a n + b, the number of the pair; Row = a; Col = b;
Total, the sum; Expo, the exponent (p - ϱ) mod p. -/
abbrev Mat : ℕ := 0
@[inherit_doc Mat] abbrev Residues : ℕ := 1
@[inherit_doc Mat] abbrev Places : ℕ := 2
@[inherit_doc Mat] abbrev Num : ℕ := 3
@[inherit_doc Mat] abbrev Prime : ℕ := 4
@[inherit_doc Mat] abbrev Square : ℕ := 5
@[inherit_doc Mat] abbrev Idx : ℕ := 6
@[inherit_doc Mat] abbrev Row : ℕ := 7
@[inherit_doc Mat] abbrev Col : ℕ := 8
@[inherit_doc Mat] abbrev Total : ℕ := 9
@[inherit_doc Mat] abbrev Expo : ℕ := 10

end CountZero

open CountZero in
/-- The term of the pair (a, b) is added to the sum. -/
def countZeroAdd : Stmt :=
  .set Expo (M (v Residues +' v Idx)) ;;
  .ite (v Expo =' k 0) .skip (.set Expo (v Prime -' v Expo)) ;;
  .set Total (v Total
    +' M (v Mat +' (k 2 *' M (v Places +' v Row) +' M (v Places +' v Col)) *' v Prime +' v Expo))

open CountZero in
/-- countZero(rm, rab, mort, n, p).  The sum is returned in local 0. -/
def countZeroBody : Stmt :=
  .set Square (v Num *' v Num) ;;
  .set Row (k 0) ;;
  .set Col (k 0) ;;
  .set Total (k 0) ;;
  .for Idx (v Square) (countZeroAdd ;; nextPair Row Col Num) ;;
  .set 0 (v Total)

/-- An upper bound on the number of steps of countZero. -/
def countZeroTime (n : ℕ) : ℕ := 60 * (n * n) + 30

/-- The term of the pair number i: the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]. -/
def countTerm (n p : ℕ) (RM : List ℤ) (RAB : List ℕ) (i : ℕ) : ℤ :=
  RM.getD (zIdx (i / n) (i % n) * p + (p - RAB.getD i 0) % p) 0

/-- What countZero needs: where the arrays lie, and what they hold.  RM is the list of the 4^K p
coefficients at rm, of absolute value at most V, and RAB is the list of the n² residues at rab. -/
structure CountZeroPre (lim : Limits) (μ : ℕ → ℤ) (rm rab mort n K p : ℕ) (RM : List ℤ)
    (RAB : List ℕ) (V : ℤ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  mat : ArrayAt μ rm RM (4 ^ K * p) V lim.space
  res : IndexAt μ rab RAB (n * n) p lim.space
  table : ListAt μ mort (spreadList (2 ^ K)) (2 ^ K) lim.space
  n_le : n ≤ 2 ^ K
  rm_lt : rm + 4 ^ K * p < lim.space
  sum_le : ((n * n : ℕ) : ℤ) * V ≤ lim.word

namespace CountZeroPre

variable {μ : ℕ → ℤ} {rm rab mort n K p : ℕ} {RM : List ℤ} {RAB : List ℕ} {V : ℤ} {t : ℕ}

/-- The place of the term of the pair number t lies in the list RM of the 4^K p coefficients. -/
theorem index_lt (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) (ht : t < n * n) :
    zIdx (t / n) (t % n) * p + (p - RAB.getD t 0) % p < 4 ^ K * p := by
  have := pre.n_le
  have := pre.res.getD_lt ht
  have : t / n < n := Nat.div_lt_of_lt_mul' ht
  have : t % n < n := Nat.mod_lt_of_lt_mul ht
  exact Nat.mul_add_lt_mul (zIdx_lt (by omega) (by omega)) (Nat.mod_lt _ (by omega))

/-- The term of the pair number t. -/
theorem readTerm (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) (ht : t < n * n) :
    μ (rm + (zIdx (t / n) (t % n) * p + (p - RAB.getD t 0) % p)) = countTerm n p RM RAB t :=
  pre.mat.read (pre.index_lt ht)

theorem abs_countTerm_le (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) (ht : t < n * n) :
    |countTerm n p RM RAB t| ≤ V := by
  rw [← pre.readTerm ht]
  exact pre.mat.abs_read_le (pre.index_lt ht)

end CountZeroPre

variable {μ : ℕ → ℤ} {rm rab mort n K p : ℕ} {RM : List ℤ} {RAB : List ℕ} {V : ℤ}

open CountZero in
/-- **The term of the pair number t is added.** -/
theorem countZeroAdd_spec (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) {t : ℕ}
    (ht : t < n * n) (S ex : ℤ) (hfits : |S + countTerm n p RM RAB t| ≤ lim.word) :
    Ends lim P d countZeroAdd
      ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, (t / n : ℕ), (t % n : ℕ), S, ex], μ⟩ 34
      fun σ' => ∃ ex' : ℤ, σ' = ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, (t / n : ℕ),
        (t % n : ℕ), S + countTerm n p RM RAB t, ex'], μ⟩ := by
  light_facts pre pre.mat pre.res pre.table
  have hrow : t / n < n := Nat.div_lt_of_lt_mul' ht
  have hcol : t % n < n := Nat.mod_lt_of_lt_mul ht
  have hreadA : μ (mort + t / n) = (spread (t / n) : ℕ) :=
    seg_spreadList_get pre.table.seg (by omega)
  have hreadB : μ (mort + t % n) = (spread (t % n) : ℕ) :=
    seg_spreadList_get pre.table.seg (by omega)
  have hreadR := pre.res.read ht
  have hrho := pre.res.getD_lt ht
  have hidx := pre.index_lt ht
  have hterm := pre.readTerm ht
  have hp : p ≤ 4 ^ K * p := Nat.le_mul_of_pos_left p (by positivity)
  replace hfits := abs_le.1 hfits
  generalize countTerm n p RM RAB t = term at *
  generalize RAB.getD t 0 = rho at *
  unfold zIdx at hidx hterm
  generalize t / n = a at *
  generalize t % n = b at *
  generalize spread a = sa at *
  generalize spread b = sb at *
  -- ex := rab[t]
  light_set (rho : ℕ) using hreadR
  -- if ex ≠ 0 then ex := p - ex
  have label : Ends lim P d (.ite (v Expo =' k 0) .skip (.set Expo (v Prime -' v Expo)))
      ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, a, b, S, (rho : ℕ)], μ⟩ 8 fun σ' =>
        σ' = ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, a, b, S, ((p - rho) % p : ℕ)], μ⟩ := by
    refine Ends.iteLast (fun h0 => Ends.skip ?_) fun h0 => Ends.setTo (p - rho : ℕ) ?_
    · obtain rfl : rho = 0 := by simpa using h0
      rw [Nat.sub_zero, Nat.mod_self]
    · have h0 : rho ≠ 0 := by simpa using h0
      rw [Nat.mod_eq_of_lt (by omega)]
      rfl
  refine Ends.next 8 (label.mono le_rfl ?_)
  rintro _ rfl
  generalize (p - rho) % p = s at hidx hterm
  -- sum := sum + rm[(2 mort[a] + mort[b]) p + ex]
  have hidxZ : (2 * (sa : ℤ) + sb) * p + s < (4 ^ K * p : ℕ) := by exact_mod_cast hidx
  have hle : 2 * (sa : ℤ) + sb ≤ (2 * (sa : ℤ) + sb) * p :=
    le_mul_of_one_le_right (by positivity) (by exact_mod_cast (by omega : 1 ≤ p))
  have haddr : ((rm : ℤ) + (2 * (sa : ℤ) + sb) * p + s).toNat = rm + ((2 * sa + sb) * p + s) := by
    rw [show (rm : ℤ) + (2 * (sa : ℤ) + sb) * p + s = ((rm + ((2 * sa + sb) * p + s) : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]
  light_set (S + term) using hreadA, hreadB, haddr, hterm
  exact ⟨_, rfl⟩

open CountZero in
/-- **countZero** returns the count and leaves the memory as it was. -/
theorem countZero_spec (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) :
    Ends lim P d countZeroBody ⟨frame [rm, rab, mort, n, p], μ⟩ (countZeroTime n) fun σ' =>
      σ'.loc 0 = countBy n p RM RAB ∧ σ'.mem = μ := by
  light_facts pre pre.mat pre.res pre.table
  unfold countZeroTime
  -- nn := n n; a := 0; b := 0; sum := 0
  light_set (n * n : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- for t < nn
  refine Ends.next _ (Ends.for (fun t σ => ∃ ex : ℤ,
      σ = ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, (t / n : ℕ), (t % n : ℕ),
        ∑ i ∈ Finset.range t, countTerm n p RM RAB i, ex], μ⟩ ∧
      |∑ i ∈ Finset.range t, countTerm n p RM RAB i| ≤ t * V) (n * n) 48
    ?start ?round ?done ?bound (hT := le_rfl))
  case start =>
    refine ⟨0, ?_, by simp⟩
    rw [update_frame_setLocal, ← frame_append_zeros _ 1, Nat.zero_div, Nat.zero_mod]
    rfl
  case bound =>
    rintro t _ - - ⟨ex, rfl, -⟩
    simp
  case round =>
    rintro t _ ht - ⟨ex, rfl, hsum⟩
    have hV := pre.abs_countTerm_le ht
    -- The new sum fits in a word.
    have hnew : |∑ i ∈ Finset.range (t + 1), countTerm n p RM RAB i| ≤ ((t + 1 : ℕ) : ℤ) * V := by
      rw [Finset.sum_range_succ]
      refine (abs_add_le _ _).trans ?_
      push_cast
      linarith
    have hfits := hnew.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast ht)
      ((abs_nonneg _).trans hV)).trans pre.sum_le)
    rw [Finset.sum_range_succ] at hfits
    refine Ends.next 34 ((countZeroAdd_spec pre ht _ ex hfits).mono le_rfl ?_)
    rintro _ ⟨ex', rfl⟩
    have hn : 0 < n := Nat.pos_of_ne_zero fun e => by simp [e] at ht
    refine Ends.nextPair ?_ hn (by omega) (by omega) rfl rfl rfl
    exact ⟨by simp, ex', by rw [update_frame_setLocal, Finset.sum_range_succ]; rfl, hnew⟩
  case done =>
    rintro _ - ⟨ex, rfl, -⟩
    -- return sum
    light_set (∑ i ∈ Finset.range (n * n), countTerm n p RM RAB i)
    exact ⟨(List.sum_map_range _ _).symm, rfl⟩

/-- **countZero** as a procedure. -/
theorem countZero_meets {μ : ℕ → ℤ} {q rm rab mort n K p : ℕ} {RM : List ℤ} {RAB : List ℕ} {V : ℤ}
    (hP : P[q]? = some countZeroBody) (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) :
    Meets lim P q d [rm, rab, mort, n, p] μ (countZeroTime n) fun r μ' =>
      r = countBy n p RM RAB ∧ μ' = μ :=
  Meets.of_body hP (countZero_spec pre)


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The count for one prime (proof of Theorem 17, "Hashing modulo a prime")

"For every prime p in the range we count the triples with S(a,b,c) ≡ 0 (mod p)", where S(a,b,c) =
w(a,b) + w(b,c) + w(a,c) is the weight of the triangle.  "Let P[a,c] := x^{w(a,c) mod p} and Q[c,b]
:= x^{w(b,c) mod p} be matrices over the ring ℤ[x]/(x^p - 1) […]; then F(p) + Z₀ is the sum over the
pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]."  Here F(p) is the number
of triples with S(a,b,c) ≠ 0 and p ∣ S(a,b,c), and Z₀ the number of triples with S(a,b,c) = 0.

countPrime(n, ab, bc, ac, p, len, K, N2, w) computes this count for one prime, in a work area at w.
Two letters of the quotation mean something else in the code.  There w is the address of the work
area, and the weights are the three lists ab, bc and ac.  And `P` is the program, while the matrices
P and Q occur only as the lists `matPList` and `matQList`.

The routine has three parts.

* The addresses of the parts of the work area (`cpAddr_spec`); they lie one behind the other
  (`cp_places`).
* Six tables: the doubles of p, the residues of the three lists of weights, the places of the
  Z-order, and the sizes 4^i p of the matrices of Strassen's recursion, which szTable(dst, p, J)
  writes (`szTable_spec`, `cpTables_spec`, `CpTabs`).
* The matrices P and Q in Z-order, their product by Strassen's algorithm, and the sum of the
  coefficients (`cpProduct_spec`).

`countPrime_spec` puts the three parts together.
-/





/-! ## The program -/

/-- The numbers of the procedures that countPrime calls. -/
structure CpNums : Type where
  pDbl : ℕ
  pResid : ℕ
  pResidues : ℕ
  pSpread : ℕ
  pSz : ℕ
  pBuild : ℕ
  pCount : ℕ
  str : StrNums

/-- The program holds the procedures that countPrime calls. -/
structure CpCtx (P : Program) (ν : CpNums) : Prop where
  hDbl : P[ν.pDbl]? = some dblTableBody
  hResid : P[ν.pResid]? = some residBody
  hResidues : P[ν.pResidues]? = some (residuesBody ν.pResid)
  hSpread : P[ν.pSpread]? = some spreadTableBody
  hSz : P[ν.pSz]? = some szTableBody
  hBuild : P[ν.pBuild]? = some buildZBody
  hCount : P[ν.pCount]? = some countZeroBody
  str : StrProg P ν.str

namespace CountPrime

/-- The local variables of countPrime.  The arguments n, ab, bc, ac, p, len, K, N2, w: N2 = 2^K is
the number of rows and columns of the padded matrices, and w, the address of the work area, is also
the address of the table of doubles.  Then n²; the addresses of the residues of the lists ab, bc and
ac, of the table of places and of the table of sizes; the size 4^K p of a matrix; the addresses
of P, Q, PQ and of the scratch space of Strassen's algorithm; a local that takes the results of the
calls, except the last one, whose result (the count) goes to local 0 and is returned. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev ListAB : ℕ := 1
@[inherit_doc Num] abbrev ListBC : ℕ := 2
@[inherit_doc Num] abbrev ListAC : ℕ := 3
@[inherit_doc Num] abbrev Prime : ℕ := 4
@[inherit_doc Num] abbrev Len : ℕ := 5
@[inherit_doc Num] abbrev Level : ℕ := 6
@[inherit_doc Num] abbrev Rows : ℕ := 7
@[inherit_doc Num] abbrev Work : ℕ := 8
@[inherit_doc Num] abbrev Square : ℕ := 9
@[inherit_doc Num] abbrev ResAB : ℕ := 10
@[inherit_doc Num] abbrev ResBC : ℕ := 11
@[inherit_doc Num] abbrev ResAC : ℕ := 12
@[inherit_doc Num] abbrev Places : ℕ := 13
@[inherit_doc Num] abbrev Sizes : ℕ := 14
@[inherit_doc Num] abbrev Size : ℕ := 15
@[inherit_doc Num] abbrev MatP : ℕ := 16
@[inherit_doc Num] abbrev MatQ : ℕ := 17
@[inherit_doc Num] abbrev MatR : ℕ := 18
@[inherit_doc Num] abbrev Scr : ℕ := 19
@[inherit_doc Num] abbrev Res : ℕ := 20

end CountPrime

open CountPrime in
/-- The first part of countPrime: the addresses of the parts of the work area. -/
def cpAddr : Stmt :=
  .set Square (v Num *' v Num) ;;
  .set ResAB (v Work +' v Len +' k 1) ;;
  .set ResBC (v ResAB +' v Square) ;;
  .set ResAC (v ResBC +' v Square) ;;
  .set Places (v ResAC +' v Square) ;;
  .set Sizes (v Places +' v Rows) ;;
  .set Size (v Rows *' v Rows *' v Prime) ;;
  .set MatP (v Sizes +' v Level +' k 1) ;;
  .set MatQ (v MatP +' v Size) ;;
  .set MatR (v MatQ +' v Size) ;;
  .set Scr (v MatR +' v Size)

open CountPrime in
/-- The second part: the table of doubles, the residues of the three lists, the table of places, the
table of sizes. -/
def cpTables (ν : CpNums) : Stmt :=
  .call ν.pDbl [v Work, v Prime, v Len] Res ;;
  .call ν.pResidues [v ListAB, v ResAB, v Square, v Work, v Len] Res ;;
  .call ν.pResidues [v ListBC, v ResBC, v Square, v Work, v Len] Res ;;
  .call ν.pResidues [v ListAC, v ResAC, v Square, v Work, v Len] Res ;;
  .call ν.pSpread [v Places, v Rows] Res ;;
  .call ν.pSz [v Sizes, v Prime, v Level] Res

open CountPrime in
/-- The third part: the matrices P and Q, their product, the count. -/
def cpProduct (ν : CpNums) : Stmt :=
  .call ν.pBuild [v MatP, v ResAC, v Places, v Num, v Rows, v Prime, k 2, k 1] Res ;;
  .call ν.pBuild [v MatQ, v ResBC, v Places, v Num, v Rows, v Prime, k 1, k 2] Res ;;
  .call ν.str.pStr [v MatR, v MatP, v MatQ, v Level, v Sizes, v Prime, v Scr] Res ;;
  .call ν.pCount [v MatR, v ResAB, v Places, v Num, v Prime] Num

/-- countPrime(n, ab, bc, ac, p, len, K, N2, w). -/
def countPrimeBody (ν : CpNums) : Stmt := cpAddr ;; cpTables ν ;; cpProduct ν

/-- The number of cells of the work area of countPrime.  (The last summand is not written; it is
room that Strassen's algorithm asks for.) -/
def countCells (n p len K : ℕ) : ℕ :=
  (len + 1) + 3 * (n * n) + 2 ^ K + (K + 1) + 3 * (4 ^ K * p) + strScr p K + (8 * (4 ^ K * p) + 1)

/-- An upper bound on the number of steps of countPrime. -/
def countTime (n p len K : ℕ) : ℕ :=
  tDblTable len + 3 * tResidues (n * n) len + (30 * 2 ^ K + 17) + tSzTable K +
    2 * buildZTime n (2 ^ K) p + strSteps p K + countZeroTime n + 150

/-! ## The layout of the work area -/

/-- The address of the residues of the list ab. -/
def cpRab (w len : ℕ) : ℕ := w + (len + 1)

/-- The address of the residues of the list bc. -/
def cpRbc (w len n : ℕ) : ℕ := cpRab w len + n * n

/-- The address of the residues of the list ac. -/
def cpRac (w len n : ℕ) : ℕ := cpRbc w len n + n * n

/-- The address of the table of places. -/
def cpMort (w len n : ℕ) : ℕ := cpRac w len n + n * n

/-- The address of the table of sizes. -/
def cpSzt (w len n K : ℕ) : ℕ := cpMort w len n + 2 ^ K

/-- The address of the matrix P. -/
def cpPm (w len n K : ℕ) : ℕ := cpSzt w len n K + (K + 1)

/-- The address of the matrix Q. -/
def cpQm (w len n K p : ℕ) : ℕ := cpPm w len n K + 4 ^ K * p

/-- The address of the product. -/
def cpRm (w len n K p : ℕ) : ℕ := cpQm w len n K p + 4 ^ K * p

/-- The address of the scratch space of Strassen's algorithm. -/
def cpScr (w len n K p : ℕ) : ℕ := cpRm w len n K p + 4 ^ K * p

/-- The parts of the work area lie one behind the other; as one fact. -/
theorem cp_places (w len n K p : ℕ) :
    cpRab w len = w + (len + 1) ∧ cpRbc w len n = cpRab w len + n * n ∧
      cpRac w len n = cpRbc w len n + n * n ∧ cpMort w len n = cpRac w len n + n * n ∧
      cpSzt w len n K = cpMort w len n + 2 ^ K ∧ cpPm w len n K = cpSzt w len n K + (K + 1) ∧
      cpQm w len n K p = cpPm w len n K + 4 ^ K * p ∧
      cpRm w len n K p = cpQm w len n K p + 4 ^ K * p ∧
      cpScr w len n K p = cpRm w len n K p + 4 ^ K * p ∧
      w + countCells n p len K = cpScr w len n K p + strScr p K + (8 * (4 ^ K * p) + 1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [cpScr, cpRm, cpQm, cpPm, cpSzt, cpMort, cpRac, cpRbc, cpRab, countCells]
  omega

/-- The local variables of countPrime after its first part. -/
@[simp] def cpFrame (n ab bc ac p len K w : ℕ) : List ℤ :=
  [n, ab, bc, ac, p, len, K, (2 ^ K : ℕ), w, (n * n : ℕ), cpRab w len, cpRbc w len n,
    cpRac w len n, cpMort w len n, cpSzt w len n K, (4 ^ K * p : ℕ), cpPm w len n K,
    cpQm w len n K p, cpRm w len n K p, cpScr w len n K p]

/-- **The first part of countPrime**, in 50 steps. -/
theorem cpAddr_spec {μ : ℕ → ℤ} {n ab bc ac p len K w : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hp : 1 ≤ p) (hcells : w + countCells n p len K ≤ lim.space) :
    Ends lim P d cpAddr ⟨frame [n, ab, bc, ac, p, len, K, (2 ^ K : ℕ), w], μ⟩ 50 fun σ' =>
      σ' = ⟨frame (cpFrame n ab bc ac p len K w), μ⟩ := by
  have := cp_places w len n K p
  have hsq : ((2 ^ K : ℕ) : ℤ) * ((2 ^ K : ℕ) : ℤ) = ((4 ^ K : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← mul_pow]
    norm_num
  have hsize : ((4 ^ K : ℕ) : ℤ) * p = ((4 ^ K * p : ℕ) : ℤ) := by push_cast; ring
  have : 4 ^ K ≤ 4 ^ K * p := Nat.le_mul_of_pos_right _ hp
  rw [cpFrame]
  generalize 4 ^ K * p = size at *
  generalize 4 ^ K = F at *
  generalize 2 ^ K = N2 at *
  refine Ends.setToThen (n * n : ℕ) <| Ends.setToThen (cpRab w len) <|
    Ends.setToThen (cpRbc w len n) <| Ends.setToThen (cpRac w len n) <|
    Ends.setToThen (cpMort w len n) <| Ends.setToThen (cpSzt w len n K) <|
    Ends.setToThen size (he := by light_side [hsq, hsize]) <|
    Ends.setToThen (cpPm w len n K) <| Ends.setToThen (cpQm w len n K p) <|
    Ends.setToThen (cpRm w len n K p) <| Ends.setTo (cpScr w len n K p) rfl

/-! ## What countPrime assumes -/

/-- What countPrime needs: the three lists of n² weights of absolute value at most U < 2^len lie
below the work area, the work area lies in the memory, and the numbers that are formed fit in a
word. -/
structure CountPrimePre (lim : Limits) (d : ℕ) (μ : ℕ → ℤ) (x : TriInst) (p len K w : ℕ) :
    Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  inst : x.Pre μ w
  p_pos : 1 ≤ p
  hK : K = Nat.clog 2 x.n
  hU : x.U < 2 ^ len
  cells : w + countCells x.n p len K ≤ lim.space
  wordDbl : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word
  wordStr : ((4 * (16 ^ K * p) : ℕ) : ℤ) ≤ lim.word
  wordSum : ((x.n * x.n * (16 ^ K * p) : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 * K + 2 ≤ lim.depth

/-- A list of residues is as long as the list of numbers. -/
@[simp] theorem length_residList (p : ℕ) (l : List ℤ) : (residList p l).length = l.length := by
  simp [residList]

/-- Residues modulo p are below p. -/
theorem lt_of_mem_residList {p : ℕ} (hp : 1 ≤ p) {l : List ℤ} {x : ℕ} (hx : x ∈ residList p l) :
    x < p := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact resid_lt (by omega) w

section Premise

variable {μ : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}

/-- The constant 4 fits in a word. -/
theorem CountPrimePre.four_le_word (pre : CountPrimePre lim d μ x p len K w) :
    (4 : ℤ) ≤ lim.word := by
  refine le_trans ?_ pre.wordStr
  have : 1 ≤ 16 ^ K * p := Nat.mul_pos (by positivity) pre.p_pos
  exact_mod_cast (by omega : 4 ≤ 4 * (16 ^ K * p))

/-- The size of a matrix fits in a word. -/
theorem CountPrimePre.size_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((4 ^ K * p : ℕ) : ℤ) ≤ lim.word := by
  have : 4 ^ K * p ≤ 16 ^ K * p := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) K)
  exact le_trans (by exact_mod_cast (by omega : 4 ^ K * p ≤ 4 * (16 ^ K * p))) pre.wordStr

/-- The number of entries of a matrix fits in a word. -/
theorem CountPrimePre.sq_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((2 ^ K * 2 ^ K : ℕ) : ℤ) ≤ lim.word := by
  rw [show 2 ^ K * 2 ^ K = 4 ^ K by rw [← mul_pow]; norm_num]
  exact le_trans (by exact_mod_cast Nat.le_mul_of_pos_right _ pre.p_pos) pre.size_le_word

/-- The entries of the table of doubles fit in a word. -/
theorem CountPrimePre.dbl_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word := by
  refine le_trans ?_ pre.wordDbl
  exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ len))

end Premise

/-! ## The procedures that countPrime calls -/

section meets

variable {μ : ℕ → ℤ}

/-- **dblTable** as a procedure. -/
theorem dblTable_meets {q dst p len : ℕ} (hP : P[q]? = some dblTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + (len + 1) ≤ lim.space)
    (hp : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, len] μ (tDblTable len) fun _ μ' =>
      Seg μ' dst (dblList p len) ∧ SameOutside μ μ' dst (len + 1) :=
  Meets.of_body hP (dblTable_spec hw hdst hp)

/-- **residues** as a procedure. -/
theorem residues_meets {q pResid src dst m dbl p len U : ℕ} {l : List ℤ}
    (hP : P[q]? = some (residuesBody pResid)) (hR : P[pResid]? = some residBody)
    (hd : d < lim.depth) (pre : ResiduesPre lim μ src dst m dbl p len U l) :
    Meets lim P q d [src, dst, m, dbl, len] μ (tResidues m len) fun _ μ' =>
      SegN μ' dst (residList p l) ∧ SameOutside μ μ' dst m :=
  Meets.of_body hP (residues_spec hR hd pre)

end meets

/-! ## The tables -/

/-- The tables of countPrime are in their places. -/
structure CpTabs (μ : ℕ → ℤ) (x : TriInst) (p len K w : ℕ) : Prop where
  dbl : Seg μ w (dblList p len)
  rab : SegN μ (cpRab w len) (residList p x.AB)
  rbc : SegN μ (cpRbc w len x.n) (residList p x.BC)
  rac : SegN μ (cpRac w len x.n) (residList p x.AC)
  mort : Seg μ (cpMort w len x.n) (spreadList (2 ^ K))
  szt : Seg μ (cpSzt w len x.n K) (szList p K)

section parts

variable {ν : CpNums} {μ₀ μ μ' : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}

/-- The tables stay in their places when only cells behind them change. -/
theorem CpTabs.keep (tabs : CpTabs μ x p len K w) (pre : CountPrimePre lim d μ₀ x p len K w)
    (hs : Kept μ μ' (cpPm w len x.n K) := by light_keep) : CpTabs μ' x p len K w := by
  have := cp_places w len x.n K p
  have := Nat.one_le_two_pow (n := K)
  have := length_spreadList (2 ^ K)
  light_facts pre.inst
  exact ⟨tabs.dbl.keep, tabs.rab.keep, tabs.rbc.keep, tabs.rac.keep, tabs.mort.keep,
    tabs.szt.keep⟩

/-- What a call of residues from countPrime assumes: the list l of weights at src lies below the
work area, the table of doubles is written, and the residues go to dst, behind that table. -/
theorem CountPrimePre.residuesPre (pre : CountPrimePre lim d μ₀ x p len K w)
    {src dst : ℕ} {l : List ℤ} (segDbl : Seg μ w (dblList p len)) (segSrc : Seg μ src l)
    (hlen : l.length = x.n * x.n) (hle : AbsLe l x.U) (hsrc : src + x.n * x.n ≤ w)
    (hdst : w + (len + 1) ≤ dst) (hend : dst + x.n * x.n ≤ lim.space) :
    ResiduesPre lim μ src dst (x.n * x.n) w p len x.U l := by
  have cells := pre.cells
  exact ⟨pre.space_le, pre.p_pos, segDbl, segSrc, hlen, hle, pre.hU, by omega, by omega, hend,
    by omega, Or.inr (by omega), Or.inr (by omega), pre.wordDbl⟩

open CountPrime in
/-- **The second part of countPrime** writes the six tables. -/
theorem cpTables_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ x p len K w) :
    Ends lim P d (cpTables ν) ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w), μ⟩
      (tDblTable len + 3 * tResidues (x.n * x.n) len + (30 * 2 ^ K + 17) + tSzTable K + 35)
      fun σ' => ∃ (r : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w ++ [r]), μ'⟩ ∧
          CpTabs μ' x p len K w ∧ SameOutside μ μ' w (countCells x.n p len K) := by
  have := cp_places w len x.n K p
  have := Nat.one_le_two_pow (n := K)
  have := length_spreadList (2 ^ K)
  have cells := pre.cells
  have depth := pre.depth
  light_facts pre.inst
  -- the table of doubles
  light_call (dblTable_meets (dst := w) ctx.hDbl pre.space_le (by omega) pre.dbl_le_word)
    with _ μ₁ ⟨dbl₁, rest₁⟩
  -- the residues of the list ab
  light_call (residues_meets ctx.hResidues ctx.hResid (by omega)
    (pre.residuesPre (dst := cpRab w len) dbl₁ pre.inst.segAB.keep pre.inst.lenAB pre.inst.leAB
      pre.inst.belowAB (by omega) (by omega))) with _ μ₂ ⟨rab₂, rest₂⟩
  -- the residues of the list bc
  light_call (residues_meets ctx.hResidues ctx.hResid (by omega)
    (pre.residuesPre (dst := cpRbc w len x.n) dbl₁.keep pre.inst.segBC.keep pre.inst.lenBC
      pre.inst.leBC pre.inst.belowBC (by omega) (by omega))) with _ μ₃ ⟨rbc₃, rest₃⟩
  -- the residues of the list ac
  light_call (residues_meets ctx.hResidues ctx.hResid (by omega)
    (pre.residuesPre (dst := cpRac w len x.n) dbl₁.keep pre.inst.segAC.keep pre.inst.lenAC
      pre.inst.leAC pre.inst.belowAC (by omega) (by omega))) with _ μ₄ ⟨rac₄, rest₄⟩
  -- the table of places
  light_call (spreadTable_meets (dst := cpMort w len x.n) ctx.hSpread pre.space_le
    pre.four_le_word pre.sq_le_word (by omega)) with _ μ₅ ⟨mort₅, rest₅⟩
  -- the table of sizes
  light_call (szTable_meets (dst := cpSzt w len x.n K) ctx.hSz pre.space_le pre.four_le_word
    (by omega) pre.size_le_word) with r μ₆ ⟨szt₆, rest₆⟩
  -- Each call has written behind the tables that were there.
  exact ⟨r, μ₆, rfl, ⟨dbl₁.keep, rab₂.keep, rbc₃.keep, rac₄.keep, mort₅.keep, szt₆⟩,
    by light_keep⟩

/-! ## The product and the count -/

/-- What a call of buildZ from countPrime assumes: the residues R stand at r, one of the three lists
of residues, and the matrix goes to dst, behind the tables. -/
theorem CountPrimePre.buildZPre (pre : CountPrimePre lim d μ₀ x p len K w)
    (tabs : CpTabs μ x p len K w) {dst r : ℕ} {l : List ℤ} (segR : SegN μ r (residList p l))
    (hlen : l.length = x.n * x.n) (hr : r + x.n * x.n ≤ cpMort w len x.n)
    (hdst : cpPm w len x.n K ≤ dst) (hend : dst + 4 ^ K * p ≤ cpScr w len x.n K p) :
    BuildZPre lim μ dst r (cpMort w len x.n) x.n K p (residList p l) := by
  have := cp_places w len x.n K p
  have := Nat.one_le_two_pow (n := K)
  have cells := pre.cells
  exact
    { space_le := pre.space_le
      res :=
        { len := by simp [hlen], seg := segR, lt := fun _ h => lt_of_mem_residList pre.p_pos h }
      table := { len := length_spreadList _, seg := tabs.mort }
      n_le := pre.hK ▸ Nat.le_pow_clog (by norm_num) x.n, p_pos := pre.p_pos, dst_le := by omega
      apartR := Or.inr (by omega), apartM := Or.inr (by omega) }

open CountPrime in
/-- **The third part of countPrime** returns the count. -/
theorem cpProduct_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ₀ x p len K w)
    (tabs : CpTabs μ x p len K w) (r : ℤ) :
    Ends lim P d (cpProduct ν) ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w ++ [r]), μ⟩
      (2 * buildZTime x.n (2 ^ K) p + strSteps p K + countZeroTime x.n + 36) fun σ' =>
        σ'.loc 0 = countOf x.n p x.AB x.BC x.AC ∧
          SameOutside μ σ'.mem w (countCells x.n p len K) := by
  have := cp_places w len x.n K p
  have := Nat.one_le_two_pow (n := K)
  have := pre.four_le_word
  have := pre.space_le
  have cells := pre.cells
  have depth := pre.depth
  have lenP := length_matPList x.n p K (residList p x.AC)
  -- the matrix P
  light_call (buildZ_P_meets ctx.hBuild (pre.buildZPre tabs (dst := cpPm w len x.n K) tabs.rac
    pre.inst.lenAC (by omega) le_rfl (by omega))) with _ μ₁ ⟨segP, rest₁⟩
  have tabs₁ : CpTabs μ₁ x p len K w := tabs.keep pre
  -- the matrix Q
  light_call (buildZ_Q_meets ctx.hBuild (pre.buildZPre tabs₁ (dst := cpQm w len x.n K p) tabs₁.rbc
    pre.inst.lenBC (by omega) (by omega) (by omega))) with _ μ₂ ⟨segQ, rest₂⟩
  have tabs₂ : CpTabs μ₂ x p len K w := tabs₁.keep pre
  -- the product
  light_call (strassen_spec ctx.str pre.space_le K
    { dst := cpRm w len x.n K p, a := cpPm w len x.n K, b := cpQm w len x.n K p
      szt := cpSzt w len x.n K, p := p, scr := cpScr w len x.n K p, len := 4 ^ K * p, J := K
      A := matPList x.n p K (residList p x.AC), B := matQList x.n p K (residList p x.BC)
      α := 1, β := 1 } μ₂
    { size := rfl, prime := pre.p_pos
      opA := { len := lenP, bound := absLe_matPList _ _ _ _, seg := segP.keep }
      opB := { len := length_matQList _ _ _ _, bound := absLe_matQList _ _ _ _, seg := segQ }
      table := { len := length_szList _ _, seg := tabs₂.szt }
      word := by rw [strassenBound_one_one]; exact_mod_cast pre.wordStr } _ (by omega))
    with _ μ₃ ⟨segR, rest₃⟩
  dsimp only at segR rest₃
  have tabs₃ : CpTabs μ₃ x p len K w := tabs₂.keep pre
  -- the count
  light_call (countZero_meets ctx.hCount (V := strassenBound p K 1 1)
    { space_le := pre.space_le
      mat :=
        { len := length_strassenList p K _ _ lenP (length_matQList _ _ _ _), seg := segR
          bound := absLe_strassenList p K _ _ 1 1 (absLe_matPList _ _ _ _) (absLe_matQList _ _ _ _)
            (by norm_num) (by norm_num) }
      res :=
        { len := by simp [pre.inst.lenAB], seg := tabs₃.rab
          lt := fun _ h => lt_of_mem_residList pre.p_pos h }
      table := { len := length_spreadList _, seg := tabs₃.mort }
      n_le := pre.hK ▸ Nat.le_pow_clog (by norm_num) x.n, rm_lt := by omega
      sum_le := by rw [strassenBound_one_one]; exact_mod_cast pre.wordSum })
    with _ μ₄ ⟨rfl, rfl⟩
  exact ⟨by simp [countOf, pre.hK], by light_keep⟩

/-- **countPrime** returns the count of the proof of Theorem 17 for the prime p, and changes only
cells of its work area. -/
theorem countPrime_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ x p len K w) :
    Ends lim P d (countPrimeBody ν) ⟨frame [x.n, x.ab, x.bc, x.ac, p, len, K, (2 ^ K : ℕ), w], μ⟩
      (countTime x.n p len K) fun σ' =>
        σ'.loc 0 = countOf x.n p x.AB x.BC x.AC ∧
          SameOutside μ σ'.mem w (countCells x.n p len K) := by
  unfold countTime
  -- the addresses
  light_piece (cpAddr_spec pre.space_le pre.p_pos pre.cells) with _ rfl
  -- the tables
  light_piece (cpTables_spec ctx pre) with _ ⟨r, μ₁, rfl, tabs, rest₁⟩
  -- the product and the count
  light_piece (cpProduct_spec ctx pre tabs r) with σ' ⟨hcount, rest₂⟩
  exact ⟨hcount, rest₁.trans rest₂⟩

/-- **countPrime** as a procedure. -/
theorem countPrime_meets {q : ℕ} (hP : P[q]? = some (countPrimeBody ν)) (ctx : CpCtx P ν)
    (pre : CountPrimePre lim d μ x p len K w) :
    Meets lim P q d [x.n, x.ab, x.bc, x.ac, p, len, K, (2 ^ K : ℕ), w] μ (countTime x.n p len K)
      fun r μ' =>
        r = countOf x.n p x.AB x.BC x.AC ∧ SameOutside μ μ' w (countCells x.n p len K) :=
  Meets.of_body hP (countPrime_spec ctx pre)

end parts

/-! ## Larger primes need more cells and more time -/

/-- The work area grows with p. -/
theorem countCells_mono {p q : ℕ} (h : p ≤ q) (n len K : ℕ) :
    countCells n p len K ≤ countCells n q len K := by
  have : 4 ^ K * p ≤ 4 ^ K * q := Nat.mul_le_mul_left _ h
  have := strScr_mono h K
  unfold countCells
  omega

/-- The time grows with p. -/
theorem countTime_mono {p q : ℕ} (h : p ≤ q) (n len K : ℕ) :
    countTime n p len K ≤ countTime n q len K := by
  have : 2 ^ K * 2 ^ K * p ≤ 2 ^ K * 2 ^ K * q := Nat.mul_le_mul_left _ h
  have := strSteps_mono h K
  unfold countTime buildZTime
  omega

end Light.Sec3
