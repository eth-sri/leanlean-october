/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.NextPair
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ZOrderFacts
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Strassen

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
adds the coefficient number (p - ϱ) mod p of the vector of (a, b) (`countTerm`); then it steps to the next pair.  The loop is `countZero_meets`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace CountZero

/-- The local variables of countZero.  The arguments: Mat = rm, Residues = rab, Places = mort,
Num = n, Prime = p.  Then Square = n²; Idx = t = a n + b, the number of the pair; Row = a; Col = b;
Total, the sum; Expo, the exponent (p - ϱ) mod p. -/
registers [Mat, Residues, Places, Num, Prime, Square, Idx, Row, Col, Total, Expo]

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
  have hn := pre.n_le
  have hp := pre.res.getD_lt ht
  have hrow : t / n < n := Nat.div_lt_of_lt_mul' ht
  have hcol : t % n < n := Nat.mod_lt_of_lt_mul ht
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
/-- **countZero** returns the count and leaves the memory as it was. -/
theorem countZero_meets {μ : ℕ → ℤ} {q rm rab mort n K p : ℕ} {RM : List ℤ} {RAB : List ℕ} {V : ℤ}
    (hP : P[q]? = some countZeroBody) (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) :
    Meets lim P q d [rm, rab, mort, n, p] μ (countZeroTime n) fun r μ' =>
      r = countBy n p RM RAB ∧ μ' = μ := by
  refine .of_body hP ?_;
  light_facts pre pre.mat pre.res pre.table
  unfold countZeroTime
  -- nn := n n; a := 0; b := 0; sum := 0
  light_steps
  let total (t : ℕ) := ∑ i ∈ Finset.range t, countTerm n p RM RAB i
  have hbound (t : ℕ) (ht : t ≤ n * n) : |total t| ≤ t * V := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun i hi => pre.abs_countTerm_le ((Finset.mem_range.mp hi).trans_le ht)
  refine Ends.next _ (Ends.forShape (fun t (z : ℕ × ℕ × ℤ × ℤ) ν =>
    ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, z.1, z.2.1, z.2.2.1, z.2.2.2], ν⟩)
    (fun t z ν => z.1 = t / n ∧ z.2.1 = t % n ∧ z.2.2.1 = total t ∧ ν = μ)
    (n * n) 48 (0, 0, 0, 0) ⟨by simp, by simp, by simp [total], rfl⟩ ?_ ?_ (first := ?_) (hT := le_rfl))
  · rintro t ⟨a, b, S, ex⟩ ν ht ⟨ha, hb, hS, hm⟩
    dsimp only at ha hb hS
    subst a b S ν
    let S := total t
    have hV := (abs_nonneg _).trans (pre.abs_countTerm_le ht)
    have hfits := abs_le.mp ((hbound (t + 1) (by omega)).trans
      ((mul_le_mul_of_nonneg_right (by exact_mod_cast ht) hV).trans pre.sum_le))
    have ht' : total (t + 1) = total t + countTerm n p RM RAB t := Finset.sum_range_succ ..
    rw [ht'] at hfits
    change -lim.word ≤ S + _ ∧ S + _ ≤ lim.word at hfits
    have hn : 0 < n := Nat.pos_of_ne_zero fun e => by simp_all
    unfold countZeroAdd
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
    generalize countTerm n p RM RAB t = term at *
    generalize RAB.getD t 0 = rho at *
    unfold zIdx at hidx hterm
    generalize ha : t / n = a at *
    generalize hb : t % n = b at *
    generalize spread a = sa at *
    generalize spread b = sb at *
    -- ex := rab[t]
    light_step using hreadR
    -- if ex ≠ 0 then ex := p - ex
    light_head
    refine Ends.pieceThen (T₁ := 8) (R := (· =
      ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, a, b, S, ((p - rho) % p : ℕ)], μ⟩)) ?_ ?_
    · refine Ends.iteIffLast (rho = 0) (fun h0 => Ends.skip ?_) (fun h0 => Ends.setTo (p - rho : ℕ) ?_)
      · simp [h0, S]
      · rw [Nat.mod_eq_of_lt (by omega)]
        rfl
    rintro _ rfl
    generalize (p - rho) % p = s at hidx hterm
    -- sum := sum + rm[(2 mort[a] + mort[b]) p + ex]
    have hidxZ : (2 * (sa : ℤ) + sb) * p + s < (4 ^ K * p : ℕ) := by exact_mod_cast hidx
    have hle : 2 * (sa : ℤ) + sb ≤ (2 * (sa : ℤ) + sb) * p :=
      le_mul_of_one_le_right (by positivity) (by omega)
    have haddr : ((rm : ℤ) + (2 * (sa : ℤ) + sb) * p + s).toNat = rm + ((2 * sa + sb) * p + s) := by
      lia
    light_step using hreadA, hreadB, haddr, hterm
    refine Ends.nextPair (t := t) ?_ hn (by omega) (by omega) (by simp [ha]) (by simp [hb]) rfl
    exact ⟨((t + 1) / n, (t + 1) % n, S + term, s), μ, rfl, rfl, rfl, ht'.symm, rfl⟩
  · rintro ⟨a, b, S, ex⟩ ν ⟨-, -, hS, hm⟩
    change S = total (n * n) at hS
    subst ν S
    light_step
    trivial
  · rw [update_frame_setLocal, ← frame_append_zeros _ 1]
    rfl


end Light.Sec3
