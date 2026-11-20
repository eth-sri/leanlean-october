/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.Count
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.StrassenTime
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ZOrder
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.ResidueTables

/-!
# The count for one prime (proof of Theorem 17, "Hashing modulo a prime")

"For every prime p in the range we count the triples with S(a,b,c) ≡ 0 (mod p)", where S(a,b,c) =
w(a,b) + w(b,c) + w(a,c) is the weight of the triangle.  "Let P[a,c] := x^{w(a,c) mod p} and Q[c,b]
:= x^{w(b,c) mod p} be matrices over the ring ℤ[x]/(x^p - 1) […]; then F(p) + Z₀ is the sum over the
pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]."  Here F(p) is the number
of triples with S(a,b,c) ≠ 0 and p ∣ S(a,b,c), and Z₀ the number of triples with S(a,b,c) = 0.

countPrime(n, K, ab, bc, ac, w, p, len, N2) computes this count for one prime, in a work area at w.
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

`countPrime_meets` puts the three parts together.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec
open ResidueTables (rab rbc rac top)

variable {lim : Limits} {P : Program} {d : ℕ}

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

/- The local variables of countPrime.  The arguments n, ab, bc, ac, p, len, K, N2, w: N2 = 2^K is
the number of rows and columns of the padded matrices, and w, the address of the work area, is also
the address of the table of doubles.  Then n²; the addresses of the residues of the lists ab, bc and
ac, of the table of places and of the table of sizes; the size 4^K p of a matrix; the addresses
of P, Q, PQ and of the scratch space of Strassen's algorithm; a local that takes the results of the
calls, except the last one, whose result (the count) goes to local 0 and is returned. -/
export ResidueTables (Size AdrAB AdrBC AdrAC Free ThePrime Bits SizeSq ResAB ResBC ResAC Small)
registers from 1 [Level]
registers from 8 [Rows]
registers from 14 [Places, Sizes, Volume, MatP, MatQ, MatR, Scr]

end CountPrime

open CountPrime in
/-- The first part of countPrime: the addresses of the parts of the work area. -/
def cpAddr : Stmt :=
  ResidueTables.addresses Places ;;
  .set Sizes (v Places +' v Rows) ;;
  .set Volume (v Rows *' v Rows *' v ThePrime) ;;
  .set MatP (v Sizes +' v Level +' k 1) ;;
  .set MatQ (v MatP +' v Volume) ;;
  .set MatR (v MatQ +' v Volume) ;;
  .set Scr (v MatR +' v Volume)

open CountPrime in
/-- The second part: the table of doubles, the residues of the three lists, the table of places, the
table of sizes. -/
def cpTables (ν : CpNums) : Stmt :=
  ResidueTables.body ν.pDbl ν.pResidues ;;
  .call ν.pSpread [v Places, v Rows] Small ;;
  .call ν.pSz [v Sizes, v ThePrime, v Level] Small

open CountPrime in
/-- The third part: the matrices P and Q, their product, the count. -/
def cpProduct (ν : CpNums) : Stmt :=
  .call ν.pBuild [v MatP, v ResAC, v Places, v Size, v Rows, v ThePrime, k 2, k 1] Small ;;
  .call ν.pBuild [v MatQ, v ResBC, v Places, v Size, v Rows, v ThePrime, k 1, k 2] Small ;;
  .call ν.str.pStr [v MatR, v MatP, v MatQ, v Level, v Sizes, v ThePrime, v Scr] Small ;;
  .call ν.pCount [v MatR, v ResAB, v Places, v Size, v ThePrime] Size

/-- countPrime(n, K, ab, bc, ac, w, p, len, N2). -/
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

/-- The address of the table of sizes. -/
def cpSzt (w len n K : ℕ) : ℕ := top w len n + 2 ^ K

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
    rab w len = w + (len + 1) ∧ rbc w len n = rab w len + n * n ∧
      rac w len n = rbc w len n + n * n ∧ top w len n = rac w len n + n * n ∧
      cpSzt w len n K = top w len n + 2 ^ K ∧ cpPm w len n K = cpSzt w len n K + (K + 1) ∧
      cpQm w len n K p = cpPm w len n K + 4 ^ K * p ∧
      cpRm w len n K p = cpQm w len n K p + 4 ^ K * p ∧
      cpScr w len n K p = cpRm w len n K p + 4 ^ K * p ∧
      w + countCells n p len K = cpScr w len n K p + strScr p K + (8 * (4 ^ K * p) + 1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  light_side [cpScr, cpRm, cpQm, cpPm, cpSzt, top, rac, rbc, rab, countCells]

/-- The local variables of countPrime after its first part. -/
@[simp] def cpFrame (n ab bc ac p len K w : ℕ) (r : ℤ := 0) : List ℤ :=
  ResidueTables.locals n ab bc ac w p len K (2 ^ K : ℕ) r ++
    [((top w len n : ℕ) : ℤ), cpSzt w len n K, (4 ^ K * p : ℕ), cpPm w len n K,
      cpQm w len n K p, cpRm w len n K p, cpScr w len n K p]

/-- **The first part of countPrime**, in 50 steps. -/
theorem cpAddr_spec {μ : ℕ → ℤ} {n ab bc ac p len K w : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hp : 1 ≤ p) (hcells : w + countCells n p len K ≤ lim.space) :
    Ends lim P d cpAddr ⟨frame [n, K, ab, bc, ac, w, p, len, (2 ^ K : ℕ)], μ⟩ 50 fun σ' =>
      σ' = ⟨frame (cpFrame n ab bc ac p len K w), μ⟩ := by
  have hplaces := cp_places w len n K p
  have hsq : ((2 ^ K : ℕ) : ℤ) * ((2 ^ K : ℕ) : ℤ) = ((4 ^ K : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← mul_pow]
    norm_num
  have hsize : ((4 ^ K : ℕ) : ℤ) * p = ((4 ^ K * p : ℕ) : ℤ) := by push_cast; ring
  have hle : 4 ^ K ≤ 4 ^ K * p := Nat.le_mul_of_pos_right _ hp
  rw [cpFrame]
  generalize 4 ^ K * p = size at *
  generalize 4 ^ K = F at *
  generalize 2 ^ K = N2 at *
  unfold cpAddr ResidueTables.addresses
  light_steps using hsq, hsize
  aesop

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
  wordStr : ((4 * (32 ^ K * p) : ℕ) : ℤ) ≤ lim.word
  wordSum : ((x.n * x.n * (32 ^ K * p) : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 * K + 2 ≤ lim.depth

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
  have : 1 ≤ 32 ^ K * p := Nat.mul_pos (by positivity) pre.p_pos
  omega

/-- The size of a matrix fits in a word. -/
theorem CountPrimePre.size_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((4 ^ K * p : ℕ) : ℤ) ≤ lim.word := by
  have hle : 4 ^ K * p ≤ 32 ^ K * p := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) K)
  exact le_trans (by omega) pre.wordStr

/-- The number of entries of a matrix fits in a word. -/
theorem CountPrimePre.sq_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((2 ^ K * 2 ^ K : ℕ) : ℤ) ≤ lim.word := by
  rw [show 2 ^ K * 2 ^ K = 4 ^ K by rw [← mul_pow]; norm_num]
  exact le_trans (by exact_mod_cast Nat.le_mul_of_pos_right _ pre.p_pos) pre.size_le_word

end Premise

/-! ## The tables -/

/-- The tables of countPrime are in their places. -/
structure CpTabs (μ : ℕ → ℤ) (x : TriInst) (p len K w : ℕ) : Prop
    extends ResidueTables.Tables x w p len μ where
  mort : Seg μ (top w len x.n) (spreadList (2 ^ K))
  szt : Seg μ (cpSzt w len x.n K) (szList p K)

section parts

variable {ν : CpNums} {μ₀ μ μ' : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}

/-- The tables stay in their places when only cells behind them change. -/
theorem CpTabs.keep (tabs : CpTabs μ x p len K w) (pre : CountPrimePre lim d μ₀ x p len K w)
    (hs : Kept μ μ' (cpPm w len x.n K) := by light_keep) : CpTabs μ' x p len K w := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have lenM := length_spreadList (2 ^ K)
  light_facts pre.inst.arrAB pre.inst.arrBC pre.inst.arrAC
  exact ⟨⟨tabs.dbl.keep, tabs.rab.keep, tabs.rbc.keep, tabs.rac.keep⟩, tabs.mort.keep, tabs.szt.keep⟩

/-- **The second part of countPrime** writes the six tables. -/
theorem cpTables_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ x p len K w) :
    Ends lim P d (cpTables ν) ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w), μ⟩
      (tDblTable len + 3 * tResidues (x.n * x.n) len + (30 * 2 ^ K + 17) + tSzTable K + 35)
      fun σ' => ∃ (r : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w r), μ'⟩ ∧
          CpTabs μ' x p len K w ∧ SameOutside μ μ' w (countCells x.n p len K) := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have lenM := length_spreadList (2 ^ K)
  have cells := pre.cells
  have depth := pre.depth
  light_facts pre.inst.arrAB pre.inst.arrBC pre.inst.arrAC
  unfold cpTables cpFrame
  light_piece (ResidueTables.spec ctx.hDbl ctx.hResid ctx.hResidues pre.inst.toArrays
    pre.space_le pre.p_pos pre.hU pre.wordDbl (by omega) (by omega))
    with _ ⟨r₄, μ₄, rfl, tabs₄, rest₄⟩
  -- the table of places
  light_call (spreadTable_meets (dst := top w len x.n) ctx.hSpread pre.space_le
    pre.four_le_word pre.sq_le_word (by omega)) with _ μ₅ ⟨mort₅, rest₅⟩
  -- the table of sizes
  light_call (szTable_meets (dst := cpSzt w len x.n K) ctx.hSz pre.space_le pre.four_le_word
    (by omega) pre.size_le_word) with r μ₆ ⟨szt₆, rest₆⟩
  -- Each call has written behind the tables that were there.
  exact ⟨r, μ₆, rfl, ⟨⟨tabs₄.dbl.keep, tabs₄.rab.keep, tabs₄.rbc.keep, tabs₄.rac.keep⟩, mort₅.keep, szt₆⟩,
    by light_keep⟩

/-! ## The product and the count -/

/-- What a call of buildZ from countPrime assumes: the residues R stand at r, one of the three lists
of residues, and the matrix goes to dst, behind the tables. -/
theorem CountPrimePre.buildZPre (pre : CountPrimePre lim d μ₀ x p len K w)
    (tabs : CpTabs μ x p len K w) {dst r : ℕ} {l : List ℤ} (segR : SegN μ r (residList p l))
    (hlen : l.length = x.n * x.n) (hr : r + x.n * x.n ≤ top w len x.n)
    (hdst : cpPm w len x.n K ≤ dst) (hend : dst + 4 ^ K * p ≤ cpScr w len x.n K p) :
    BuildZPre lim μ dst r (top w len x.n) x.n K p (residList p l) := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have cells := pre.cells
  exact
    { space_le := pre.space_le
      res :=
        { len := by simp [hlen], seg := segR, lt := fun _ h => lt_of_mem_residList pre.p_pos h }
      table := { len := length_spreadList _, seg := tabs.mort }
      n_le := pre.hK ▸ Nat.le_pow_clog (by norm_num) x.n, p_pos := pre.p_pos, dst_le := by omega
      apartR := Or.inr (by omega), apartM := Or.inr (by omega) }

/-- **The third part of countPrime** returns the count. -/
theorem cpProduct_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ₀ x p len K w)
    (tabs : CpTabs μ x p len K w) (r : ℤ) :
    Ends lim P d (cpProduct ν) ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w r), μ⟩
      (2 * buildZTime x.n (2 ^ K) p + strSteps p K + countZeroTime x.n + 36) fun σ' =>
        σ'.loc 0 = countOf x.n p x.AB x.BC x.AC ∧
          SameOutside μ σ'.mem w (countCells x.n p len K) := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have h4 := pre.four_le_word
  have cells := pre.cells
  have depth := pre.depth
  have lenP := length_matList false x.n p K (residList p x.AC)
  -- the matrix P
  light_call (buildZ_meets false ctx.hBuild (pre.buildZPre tabs (dst := cpPm w len x.n K) tabs.rac
    pre.inst.arrAC.len (by omega) le_rfl (by omega))) with _ μ₁ ⟨segP, rest₁⟩
  have tabs₁ : CpTabs μ₁ x p len K w := tabs.keep pre
  -- the matrix Q
  light_call (buildZ_meets true ctx.hBuild (pre.buildZPre tabs₁ (dst := cpQm w len x.n K p) tabs₁.rbc
    pre.inst.arrBC.len (by omega) (by omega) (by omega))) with _ μ₂ ⟨segQ, rest₂⟩
  have tabs₂ : CpTabs μ₂ x p len K w := tabs₁.keep pre
  -- the product
  light_call (strassen_spec ctx.str pre.space_le K
    { dst := cpRm w len x.n K p, a := cpPm w len x.n K, b := cpQm w len x.n K p
      szt := cpSzt w len x.n K, p := p, scr := cpScr w len x.n K p, len := 4 ^ K * p, J := K
      A := matPList x.n p K (residList p x.AC), B := matQList x.n p K (residList p x.BC)
      α := 1, β := 1 } μ₂
    { size := rfl, prime := pre.p_pos
      opA := { len := lenP, bound := absLe_matList false _ _ _ _, seg := segP.keep }
      opB := { len := length_matList true _ _ _ _, bound := absLe_matList true _ _ _ _, seg := segQ }
      table := { len := length_szList _ _, seg := tabs₂.szt }
      word := by rw [strassenBound_one_one]; exact_mod_cast pre.wordStr } _ (by omega))
    with _ μ₃ ⟨segR, rest₃⟩
  dsimp only at segR rest₃
  have tabs₃ : CpTabs μ₃ x p len K w := tabs₂.keep pre
  -- the count
  light_call (countZero_meets ctx.hCount (V := strassenBound p K 1 1)
    { space_le := pre.space_le
      mat :=
        { len := length_strassenList p K _ _ lenP (length_matList true _ _ _ _), seg := segR
          bound := absLe_strassenList p K _ _ 1 1 (absLe_matList false _ _ _ _) (absLe_matList true _ _ _ _)
            (by norm_num) (by norm_num) }
      res :=
        { len := by simp [pre.inst.arrAB.len], seg := tabs₃.rab
          lt := fun _ h => lt_of_mem_residList pre.p_pos h }
      table := { len := length_spreadList _, seg := tabs₃.mort }
      n_le := pre.hK ▸ Nat.le_pow_clog (by norm_num) x.n, rm_lt := by omega
      sum_le := by rw [strassenBound_one_one]; exact_mod_cast pre.wordSum })
    with _ μ₄ ⟨rfl, rfl⟩
  exact ⟨by simp [countOf, pre.hK], by light_keep⟩

/-- **countPrime** returns the count of the proof of Theorem 17 for the prime p, and changes only
cells of its work area. -/
theorem countPrime_meets {q : ℕ} (hP : P[q]? = some (countPrimeBody ν)) (ctx : CpCtx P ν)
    (pre : CountPrimePre lim d μ x p len K w) :
    Meets lim P q d [x.n, K, x.ab, x.bc, x.ac, w, p, len, (2 ^ K : ℕ)] μ (countTime x.n p len K)
      fun r μ' =>
        r = countOf x.n p x.AB x.BC x.AC ∧ SameOutside μ μ' w (countCells x.n p len K) := by
  refine .of_body hP ?_;
  unfold countTime
  -- the addresses
  light_piece (cpAddr_spec pre.space_le pre.p_pos pre.cells) with _ rfl
  -- the tables
  light_piece (cpTables_spec ctx pre) with _ ⟨r, μ₁, rfl, tabs, rest₁⟩
  -- the product and the count
  light_piece (cpProduct_spec ctx pre tabs r) with σ' ⟨hcount, rest₂⟩
  exact ⟨hcount, rest₁.trans rest₂⟩

end parts

/-! ## Larger primes need more cells and more time -/

/-- The work area grows with p. -/
theorem countCells_mono {p q : ℕ} (h : p ≤ q) (n len K : ℕ) :
    countCells n p len K ≤ countCells n q len K := by
  have hsize : 4 ^ K * p ≤ 4 ^ K * q := Nat.mul_le_mul_left _ h
  have hscr := strScr_mono h K
  unfold countCells
  omega

/-- The time grows with p. -/
theorem countTime_mono {p q : ℕ} (h : p ≤ q) (n len K : ℕ) :
    countTime n p len K ≤ countTime n q len K := by
  have hsize : 2 ^ K * 2 ^ K * p ≤ 2 ^ K * 2 ^ K * q := Nat.mul_le_mul_left _ h
  have hsteps := strSteps_mono h K
  unfold countTime buildZTime
  omega

end Light.Sec3
