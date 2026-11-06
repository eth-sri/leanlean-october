/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.CountPrime
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Primes
public import ThreeSumApsp.Spec.Sec3.Theorem17.Choice

/-!
# The choice of the prime (proof of Theorem 17, "Hashing modulo a prime")

"We reduce the weights modulo a prime p ∈ [√D/2, √D), chosen deterministically. […] For every prime
p in the range we count the triples with S(a,b,c) ≡ 0 (mod p). […] We select the prime with the
smallest count".  Here S(a,b,c) is the weight of the triangle, the sum of its entries in the three
lists of weights ab, bc and ac, and D is the parameter of Theorem 17.

choosePrime(n, U, ab, bc, ac, D, w), where w is the address of the work area, lists the primes of
the range (`primesList D`) at w, computes the number len of binary digits of U and the numbers
K = ⌈log₂ n⌉ and 2^K (`chLevel_spec`), and goes through the primes once.  A round counts for one
prime, by a call of countPrime with the work area behind the list of the primes, and keeps the prime
if it is the first one or its count is smaller than the best so far (`chKeep_spec`,
`chRound_spec`).

On the pure side, `bestOf f L i` is the first of the first i primes with the smallest count, one
more prime changes it as the program does (`BestSoFar.step`), and at the end it is the chosen prime
(`bestOf_length`).  `choosePrime_spec` is the whole routine.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The numbers of the procedures that choosePrime calls. -/
structure ChNums where
  (pPrimes pBitLen pCountPrime : ℕ)
  cp : CpNums
  pSqrt : ℕ
  pSieve : ℕ

/-- The program holds the procedures that choosePrime calls. -/
structure ChCtx (P : Program) (ν : ChNums) : Prop where
  hPrimes : P[ν.pPrimes]? = some (primesBody ν.pSqrt ν.pSieve)
  hBitLen : P[ν.pBitLen]? = some bitLenBody
  hCountPrime : P[ν.pCountPrime]? = some (countPrimeBody ν.cp)
  cp : CpCtx P ν.cp
  primes : Primes.Ctx P ν.pSqrt ν.pSieve


/-- K = ⌈log₂ n⌉ and 2^K, by doubling. -/
def chLevel  :=
  .set 9 (k 0) ;;
  .set 10 (k 1) ;;
  .while (v 10 <' v 0) (
    .set 10 (v 10 +' v 10) ;;
    .set 9 (v 9 +' k 1))

/-- The prime is kept if it is the first one or its count is smaller than the best so far. -/
def chKeep : Stmt :=
  .ite (v 12 =' k 0) (.set 15 (v 13) ;; .set 16 (v 14))
    (.ite (v 14 <' v 16) (.set 15 (v 13) ;; .set 16 (v 14)) .skip)

/-- One round: the count for the prime number i. -/
def chRound (ν : ChNums)  :=
  .set 13 (M (v 6 +' v 12)) ;;
  .call ν.pCountPrime
    [v 0, v 2, v 3, v 4, v 13, v 8, v 9, v 10, v 11] 14 ;;
  chKeep

/-- choosePrime(n, U, ab, bc, ac, D, w). -/
def choosePrimeBody (ν : ChNums)  :=
  .call ν.pPrimes [v 6, v 5] 7 ;;
  .call ν.pBitLen [v 1] 8 ;;
  chLevel ;;
  .set 11 (v 6 +' v 7) ;;
  .set 15 (k 0) ;;
  .set 16 (k 0) ;;
  .for 12 (v 7) (chRound ν) ;;
  .set 0 (v 15)

/-- The number of cells that choosePrime may change, from w on: the list of the primes and the work
area of countPrime for the largest possible prime. -/
def chooseCells n U D :=
  Nat.sqrt D + countCells n (Nat.sqrt D) (bitLen U) (Nat.clog 2 n)

/-- An upper bound on the number of steps of choosePrime. -/
def chooseTime n U D :=
  tPrimes D + tBitLen U + 12 * Nat.clog 2 n +
    Nat.sqrt D * (countTime n (Nat.sqrt D) (bitLen U) (Nat.clog 2 n) + 50) + 60

/-- What choosePrime needs: the three lists of n² weights of absolute value at most U lie below w,
the cells from w on lie in the memory, and the numbers that are formed fit in a word. -/
structure ChoosePrimePre (lim : Limits) (d : ℕ) (μ : Light.Memory) (x : TriInst) (D w : ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  inst : x.Pre μ w
  cells : w + chooseCells x.n x.U D ≤ lim.space
  wordD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word
  wordU : ((2 * x.U + 2 : ℕ) : ℤ) ≤ lim.word
  wordN : ((2 * x.n + 1 : ℕ) : ℤ) ≤ lim.word
  wordDbl : ((Nat.sqrt D * 2 ^ (bitLen x.U + 1) : ℕ) : ℤ) ≤ lim.word
  wordStr : ((4 * (16 ^ Nat.clog 2 x.n * Nat.sqrt D) : ℕ) : ℤ) ≤ lim.word
  wordSum : ((x.n * x.n * (16 ^ Nat.clog 2 x.n * Nat.sqrt D) : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 * Nat.clog 2 x.n + 3 ≤ lim.depth

/-! ## The pure side: the best prime so far -/

/-- The count is not negative: it is a number of triples. -/
theorem countOf_nonneg n {p} (hp : 1 ≤ p) AB BC AC :
    0 ≤ countOf n p AB BC AC := by
  grind [countOf_eq]

/-- What the locals best and cnt hold after i primes: nothing yet, or the best prime so far and its
count c, where c q is the count for the prime q. -/
def BestSoFar (c : Light.Memory) L i (best cnt : ℤ) :=
  i = 0 ∧ best = 0 ∨
    1 ≤ i ∧ best = bestOf (fun q => (c q).toNat) L i ∧
      cnt = c (bestOf (fun q => (c q).toNat) L i) ∧ 0 ≤ cnt

/-- One more prime: it is kept if it is the first one or its count is smaller. -/
theorem BestSoFar.step {c} {L} {i} {best cnt}
    (h : BestSoFar c L i best cnt) hi (hc : 0 ≤ c L[i]) :
    BestSoFar c L (i + 1) (if i = 0 ∨ c L[i] < cnt then L[i] else best)
      (if i = 0 ∨ c L[i] < cnt then c L[i] else cnt) := by
  refine Or.inr ⟨Nat.succ_pos i, ?_⟩
  obtain ⟨rfl, -⟩ | ⟨hi1, rfl, rfl, hcnt⟩ := h
  · grind [bestOf_one]
  · rw [bestOf_succ _ L hi1 hi]
    grind

/-! ## The parts of the program -/

/-- The local variables of choosePrime during the loop over the primes. -/
@[simp] def chFrame (n U ab bc ac D w nP len K : ℕ) (i q c best cnt : ℤ) : List ℤ :=
  [n, U, ab, bc, ac, D, w, nP, len, K, 2 ^ K, w + nP, i, q, c, best, cnt]

section

variable {ν : ChNums} {μ μ' : Light.Memory} {n U ab bc ac D w nP len K : ℕ} {AB BC AC : List ℤ}

/-- **K = ⌈log₂ n⌉ and 2^K.** -/
theorem chLevel_spec (hword : ((2 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d chLevel ⟨frame [n, U, ab, bc, ac, D, w, nP, len], μ⟩ (12 * Nat.clog 2 n + 8)
      fun σ' => σ' = ⟨frame [n, U, ab, bc, ac, D, w, nP, len, Nat.clog 2 n,
        2 ^ Nat.clog 2 n], μ⟩ := by
  have test : ∀ j, 2 ^ j < n ↔ j < Nat.clog 2 n := fun j =>
    (Nat.lt_clog_iff_pow_lt (by norm_num)).symm
  generalize Nat.clog 2 n = L at test
  push_cast at hword
  -- level := 0; rows := 1
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while rows < n: rows := rows + rows; level := level + 1.  Before round j, rows = 2^j.
  refine Ends.whileBlock
    (fun j σ => σ = ⟨frame [n, U, ab, bc, ac, D, w, nP, len, j, (2 ^ j : ℕ)], μ⟩) L (by simp) ?round
    ?done
  case round =>
    rintro j _ hj rfl
    have hlt := (test j).2 hj
    have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ, Nat.mul_two]
    generalize 2 ^ j = q at hlt hjlt
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    ram_safe

/-- **Keeping the better prime.** -/
theorem chKeep_spec (h0 : 0 ≤ lim.word) (i : ℕ) q c best cnt :
    Ends lim P d chKeep ⟨frame (chFrame n U ab bc ac D w nP len K i q c best cnt), μ⟩ 12 fun σ' =>
      σ' = ⟨frame (chFrame n U ab bc ac D w nP len K i q c
        (if i = 0 ∨ c < cnt then q else best) (if i = 0 ∨ c < cnt then c else cnt)), μ⟩ := by
  refine Ends.block ⟨by simp [chKeep, h0], ?_⟩ (by simp [chKeep])
  by_cases hi : i = 0 <;> by_cases hc : c < cnt <;>
    simp [chKeep, update_frame_setLocal, hi, hc]

variable {x : TriInst}

/-- The cells that choosePrime may change lie in the memory: the list of the primes, and the work
area of countPrime. -/
theorem ChoosePrimePre.cells_le (pre : ChoosePrimePre lim d μ x D w) :
    w + (Nat.sqrt D + countCells x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n)) ≤ lim.space :=
  pre.cells

/-- What countPrime assumes holds for each prime q of the range, with the work area behind the list
of the primes, as long as only cells from w on have changed. -/
theorem ChoosePrimePre.countPre (pre : ChoosePrimePre lim d μ x D w)
    (rest : SameOutside μ μ' w (chooseCells x.n x.U D)) {q} (hq : q ∈ primesList D) :
    CountPrimePre lim (d + 1) μ' x q (bitLen x.U) (Nat.clog 2 x.n) (w + (primesList D).length) := by
  have cells := pre.cells_le
  have depth := pre.depth
  have  := length_primesList_le D
  have hqS := le_sqrt_of_mem_primesList hq
  have  := countCells_mono hqS x.n (bitLen x.U) (Nat.clog 2 x.n)
  exact
    { space_le := pre.space_le, inst := pre.inst.keep.mono (Nat.le_add_right _ _)
      p_pos := (mem_primesList.1 hq).1.one_le, hK := rfl, hU := Nat.lt_size_self x.U
      cells := by omega
      wordDbl := le_trans (by simp_all) pre.wordDbl
      wordStr := le_trans
        (by simp_all) pre.wordStr
      wordSum := le_trans
        (by gcongr) pre.wordSum
      depth := by omega }

/-- The state of choosePrime before round i: the best prime so far and its count are in their
locals, the list of the primes stands at w, and only cells from w on have changed. -/
def ChInv μ (x : TriInst) (D w i : ℕ) (σ : State) :=
  ∃ (q c best cnt : ℤ) (μ' : Light.Memory),
    σ = ⟨frame (chFrame x.n x.U x.ab x.bc x.ac D w (primesList D).length (bitLen x.U)
      (Nat.clog 2 x.n) i q c best cnt), μ'⟩ ∧
    BestSoFar (fun p => countOf x.n p x.AB x.BC x.AC) (primesList D) i best cnt ∧
    SegN μ' w (primesList D) ∧ SameOutside μ μ' w (chooseCells x.n x.U D)

variable (ctx : ChCtx P ν) (pre : ChoosePrimePre lim d μ x D w)

include ctx pre in
/-- **One round of choosePrime.** -/
theorem chRound_spec  {i }
    (hi : i < (primesList D).length) {σ } (h : ChInv μ x D w i σ) :
    Ends lim P d (chRound ν) σ (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 28)
      fun σ' => σ'.loc 12 = i ∧ ChInv μ x D w (i + 1)
        { σ' with loc := Function.update σ'.loc 12 (i + 1) } := by
  obtain ⟨q₀, c₀, best, cnt, μ', rfl, hbest, seg, rest⟩ := h
  have  := pre.space_le
  have  := pre.cells_le
  have depth := pre.depth
  have  := length_primesList_le D
  have hmem := List.getElem_mem hi
  have  := countTime_mono (le_sqrt_of_mem_primesList hmem) x.n (bitLen x.U) (Nat.clog 2 x.n)
  have  :=
    countCells_mono (le_sqrt_of_mem_primesList hmem) x.n (bitLen x.U) (Nat.clog 2 x.n)
  have hread : μ' (w + i) = (primesList D)[i] := by
    rw [seg i (by simpa using hi), List.getElem_map]
  -- prime := w[i]
  light_set ((primesList D)[i] : ℕ) using hread
  -- count := countPrime(n, ab, bc, ac, prime, len, K, 2^K, area)
  refine Ends.callToThen (countPrime_meets ctx.hCountPrime ctx.cp (pre.countPre rest hmem)) ?_
    (hT := by simp; omega)
  rintro _ μ'' ⟨rfl, rest'⟩
  -- The prime is kept if it is the first one or its count is smaller.
  refine (chKeep_spec (by omega) i _ _ best cnt).mono (by simp; omega) ?_
  rintro _ rfl
  refine ⟨by simp, ((primesList D)[i] : ℕ), countOf x.n (primesList D)[i] x.AB x.BC x.AC, _, _,
    μ'', by simp [update_frame_setLocal],
    hbest.step hi (countOf_nonneg x.n (mem_primesList.1 hmem).1.one_le x.AB x.BC x.AC),
    seg.keep, rest.trans (rest'.mono (by omega) ?_)⟩
  unfold chooseCells
  omega

/-- **primes** as a procedure. -/
theorem primes_meets {q dst pSqrt pSieve} (hP : P[q]? = some (primesBody pSqrt pSieve))
    (C : Primes.Ctx P pSqrt pSieve) (hw : (lim.space : ℤ) ≤ lim.word)
    (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + 2 * Nat.sqrt D + 1 ≤ lim.space)
    (hd : d < lim.depth) :
    Meets lim P q d [dst, D] μ (tPrimes D) fun r μ' =>
      r = (primesList D).length ∧ SegN μ' dst (primesList D) ∧
        SameOutside μ μ' dst (2 * Nat.sqrt D + 1) :=
  Meets.of_body hP (primes_spec C hw hD hdst hd)

/-- **bitLen** as a procedure. -/
theorem bitLen_meets {q} (hP : P[q]? = some bitLenBody)
    (hU : ((2 * U + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [U] μ (tBitLen U) fun r μ' => r = bitLen U ∧ μ' = μ :=
  Meets.of_body hP (bitLen_spec hU)

include ctx pre in
/-- **choosePrime** returns the first prime of the range with the smallest count (0 if the range has
no prime), and changes only cells of its work area. -/
theorem choosePrime_spec  :
    Ends lim P d (choosePrimeBody ν) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, D, w], μ⟩
      (chooseTime x.n x.U D) fun σ' =>
        σ'.loc 0 = chosenPrime x.n D x.AB x.BC x.AC ∧
          SameOutside μ σ'.mem w (chooseCells x.n x.U D) := by
  have  := pre.space_le
  have  := pre.cells_le
  have depth := pre.depth
  have  := length_primesList_le D
  have  : Nat.sqrt D + 1 ≤ countCells x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) := by
    have  : Nat.sqrt D ≤ 4 ^ Nat.clog 2 x.n * Nat.sqrt D :=
      Nat.le_mul_of_pos_left _ (by positivity)
    unfold countCells
    grind
  have hloop : (primesList D).length *
      (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 36) ≤
      Nat.sqrt D * (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 50) :=
    Nat.mul_le_mul (length_primesList_le D) (by omega)
  unfold chooseTime
  -- primes := the primes of the range, at w
  light_call (primes_meets (dst := w) ctx.hPrimes ctx.primes pre.space_le pre.wordD
    (by omega) (by omega)) with _ μ₁ ⟨rfl, seg, rest⟩
  -- len := bitLen(U)
  light_call (bitLen_meets ctx.hBitLen pre.wordU) with _ μ₂ ⟨rfl, hμ⟩
  rw [hμ]
  -- K and 2^K
  light_piece (chLevel_spec pre.wordN) with _ rfl
  -- area := w + primes; best := 0; bestCount := 0
  light_set (w + (primesList D).length : ℕ)
  light_set 0
  light_set 0
  -- for i < primes: one round
  refine Ends.next _ (Ends.for (ChInv μ x D w) (primesList D).length
    (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 28) ?start
    (fun i σ hi _ h => chRound_spec ctx pre hi h) ?done ?bound (hT := le_rfl))
    (by simp; ring_nf at hloop ⊢; omega)
  case start =>
    exact ⟨0, 0, 0, 0, μ₁, by simp [update_frame_setLocal], Or.inl ⟨rfl, rfl⟩, seg,
      rest.mono le_rfl (by unfold chooseCells; omega)⟩
  case bound =>
    rintro i _ - - ⟨q, c, best, cnt, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨q, c, best, cnt, μ', rfl, hbest, -, rest'⟩
    -- return best
    refine Ends.setTo best ⟨?_, rest'⟩ (hT := by simp; ring_nf at hloop ⊢; omega)
    change best = ((primesList D).argmin fun q => (countOf x.n q x.AB x.BC x.AC).toNat).getD 0
    obtain ⟨hnil, rfl⟩ | ⟨hpos, rfl, -, -⟩ := hbest
    · simp_all
    · rw [bestOf_length]

/-- **choosePrime** as a procedure. -/
theorem choosePrime_meets {q} (hP : P[q]? = some (choosePrimeBody ν)) (ctx : ChCtx P ν)
    (pre : ChoosePrimePre lim d μ x D w) :
    Meets lim P q d [x.n, x.U, x.ab, x.bc, x.ac, D, w] μ (chooseTime x.n x.U D) fun r μ' =>
      r = chosenPrime x.n D x.AB x.BC x.AC ∧ SameOutside μ μ' w (chooseCells x.n x.U D) :=
  Meets.of_body hP (choosePrime_spec ctx pre)

end

end Light.Sec3
