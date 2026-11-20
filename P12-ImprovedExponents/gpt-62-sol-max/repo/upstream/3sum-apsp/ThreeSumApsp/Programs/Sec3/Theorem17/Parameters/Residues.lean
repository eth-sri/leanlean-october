/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.Geometric
public import ThreeSumApsp.Lang.Lib.Logs
public import ThreeSumApsp.Lang.Lib.ArrayAt
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing
public import Mathlib.Data.Nat.Size

/-!
# Residues without division

"We reduce the weights modulo a prime p" (proof of Theorem 17).  The language has no division.  The
residue of a number w modulo p is found by greedy subtraction of 2^len p, …, 2p, p, which are kept
in a table.

* bitLen(U) returns the number of binary digits of U, by doubling (`bitLen_meets`).
* dblTable(dst, p, len) writes p, 2p, …, 2^len p to dst (`dblTable_meets`).
* resid(w, dbl, len) returns w mod p, for |w| < 2^len, given the table at dbl (`resid_meets`).  What
  the routine holds after i rounds is `greedyAt p len w i`: it is not negative, below 2^(len+1-i) p,
  and congruent to w (`greedyAt_inv`), so that it ends with the residue (`greedyAt_end`).
* residues(src, dst, m, dbl, len) writes the residues of the m numbers at src to dst, by one call of
  resid for each (`residues_meets`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The number of binary digits -/

def bitLenBody : Stmt := binaryLog true 1

def tBitLen (U : ℕ) : ℕ := 14 * bitLen U + 12

/-- **bitLen** returns the least len with U < 2^len and changes no cell. -/
theorem bitLen_meets {μ : ℕ → ℤ} {U : ℕ} {q : ℕ} (hP : P[q]? = some bitLenBody)
    (hU : ((2 * U + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [U] μ (tBitLen U) fun r μ' => r = (bitLen U : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_;
  exact binaryLog_spec true (p := 1) (by decide) (by simp; omega)
    (by simpa [bitLen] using fun j => (Nat.lt_size (n := U) (m := j)).symm)

/-! ## The table of the doubles -/

/-- The table has len + 1 entries. -/
@[simp] theorem length_dblList (p len : ℕ) : (dblList p len).length = len + 1 := by simp [dblList]

/-- Entry j of the table is 2^j p. -/
theorem read_dblList {μ : ℕ → ℤ} {dbl p len j : ℕ} (h : Seg μ dbl (dblList p len)) (hj : j ≤ len) :
    μ (dbl + j) = ((p * 2 ^ j : ℕ) : ℤ) := by
  rw [h j (by simp_all)]
  simp [dblList]

/-- dblTable(dst, p, len) writes `p, 2p, …, 2^len p`. -/
def dblTableBody : Stmt := geomTable 2

abbrev tDblTable (len : ℕ) := geomTime len

/-- The doubles table is a geometric progression of ratio 2. -/
theorem dblTable_meets {μ : ℕ → ℤ} {q dst p len : ℕ} (hP : P[q]? = some dblTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + (len + 1) ≤ lim.space)
    (hp : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, len] μ (tDblTable len) fun _ μ' =>
      Seg μ' dst (dblList p len) ∧ SameOutside μ μ' dst (len + 1) := by
  refine .of_body hP ?_;
  simpa only [dblTableBody, dblList, geomList, mul_comm] using
    (geomTable_spec (b := 2) (by decide) (fun h => (h rfl).elim) hw hdst (by simpa only [mul_comm] using hp)
      (P := P) (d := d) (μ := μ))

/-! ## One residue -/

/-- The number that resid holds after i rounds: it starts from w + 2^len p, and round number i
subtracts 2^(len-i) p if that leaves a number that is not negative. -/
def greedyAt (p len : ℕ) (w : ℤ) : ℕ → ℤ
  | 0 => w + ((p * 2 ^ len : ℕ) : ℤ)
  | i + 1 =>
    if ((p * 2 ^ (len - i) : ℕ) : ℤ) ≤ greedyAt p len w i then
      greedyAt p len w i - ((p * 2 ^ (len - i) : ℕ) : ℤ)
    else greedyAt p len w i

/-- 2^(j+1) p is twice 2^j p. -/
private theorem cast_mul_pow_succ (p j : ℕ) :
    ((p * 2 ^ (j + 1) : ℕ) : ℤ) = 2 * ((p * 2 ^ j : ℕ) : ℤ) := by
  grind

/-- After i rounds the number is not negative, below 2^(len+1-i) p, and congruent to w. -/
theorem greedyAt_inv {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) : ∀ i, i ≤ len + 1 →
    0 ≤ greedyAt p len w i ∧ greedyAt p len w i < ((p * 2 ^ (len + 1 - i) : ℕ) : ℤ) ∧
      greedyAt p len w i ≡ w [ZMOD (p : ℤ)] := by
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨hlow, hhigh⟩ := abs_lt.1 hw
    have hle : (2 : ℤ) ^ len ≤ ((p * 2 ^ len : ℕ) : ℤ) := by
      simp_all
    rw [greedyAt, Nat.sub_zero, cast_mul_pow_succ]
    exact ⟨by linarith, by linarith,
      by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨hlow, hhigh, hmod⟩ := ih (by omega)
    rw [show len + 1 - i = (len - i) + 1 by omega, cast_mul_pow_succ] at hhigh
    rw [show len + 1 - (i + 1) = len - i by omega, greedyAt]
    split_ifs with h
    all_goals (simp_all <;> omega)

/-- Greedy subtraction gives the remainder. -/
theorem greedyAt_end {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) :
    greedyAt p len w (len + 1) = (resid p w : ℕ) := by
  obtain ⟨hlow, hhigh, hmod⟩ := greedyAt_inv hp hw (len + 1) le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at hhigh
  rw [resid_cast (by omega), ← Int.emod_eq_of_lt hlow hhigh]
  exact hmod

/-- Every number that resid holds is below 2^(len+1) p. -/
theorem greedyAt_lt {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) {i : ℕ}
    (hi : i ≤ len + 1) : greedyAt p len w i < ((p * 2 ^ (len + 1) : ℕ) : ℤ) := by
  obtain ⟨-, hhigh, -⟩ := greedyAt_inv hp hw i hi
  exact hhigh.trans_le (by
    exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) (by omega)))

namespace Resid

/-- The local variables of resid: the arguments w, dbl, len; one more than the next exponent; the
number that is reduced. -/
registers [Arg, Dbl, Len, Exp, Num]

end Resid

open Resid in
/-- resid(w, dbl, len). -/
def residBody : Stmt :=
  .set Num (v Arg +' M (v Dbl +' v Len)) ;;
  .set Exp (v Len +' k 1) ;;
  .while (k 0 <' v Exp) (
    .set Exp (v Exp -' k 1) ;;
    .ite (M (v Dbl +' v Exp) ≤' v Num) (.set Num (v Num -' M (v Dbl +' v Exp))) .skip) ;;
  .set Arg (v Num)

/-- The time of resid. -/
def tResid (len : ℕ) : ℕ := 24 * len + 41

/-- **resid** returns w mod p and changes no cell.  It forms numbers up to 2^(len+1) p. -/
theorem resid_meets {μ : ℕ → ℤ} {pResid dbl p len : ℕ} {w : ℤ} (hP : P[pResid]? = some residBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p) (hseg : Seg μ dbl (dblList p len))
    (hlt : |w| < 2 ^ len) (hdbl : dbl + (len + 1) ≤ lim.space)
    (hword : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pResid d [w, dbl, len] μ (tResid len) fun r μ' => r = (resid p w : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have hlow := fun i hi => (greedyAt_inv hp hlt i hi).1
  have hhigh := fun i (hi : i ≤ len + 1) => greedyAt_lt hp hlt hi
  unfold tResid
  -- num := w + dbl[len]; exp := len + 1
  have hlow0 := hlow 0 (by omega)
  have hhigh0 := hhigh 0 (by omega)
  have hfirst : w + μ (dbl + len) = greedyAt p len w 0 := by rw [read_dblList hseg le_rfl, greedyAt]
  light_steps using hfirst
  -- while 0 < exp.  Before round i, exp = len + 1 - i and num = greedyAt p len w i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [w, dbl, len, (len + 1 - i : ℕ), greedyAt p len w i], μ⟩) (len + 1)
    (by simp) ?round ?done le_rfl) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hlowi := hlow i hi.le
    have hhighi := hhigh i hi.le
    have hread := read_dblList hseg (show len - i ≤ len by omega)
    have hexp : ((len + 1 - i : ℕ) : ℤ) - 1 = (len - i : ℕ) := by omega
    have hnext : len + 1 - (i + 1) = len - i := by omega
    have hpos : (0 : ℤ) ≤ ((p * 2 ^ (len - i) : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [hnext, greedyAt]
    generalize greedyAt p len w i = g at hlowi hhighi
    generalize ((p * 2 ^ (len - i) : ℕ) : ℤ) = q at hread hpos
    -- exp := exp - 1; if dbl[exp] ≤ num then num := num - dbl[exp]
    refine ⟨by light_side, by light_side, ?_, ?_⟩
    · light_side [Limits.Addr, hexp, hread]
    · by_cases hle : q ≤ g <;> simp [update_frame_setLocal, hexp, hread, hle]
  case done =>
    rintro _ rfl
    -- return num
    exact ⟨by light_side, by light_side,
      Ends.setTo (greedyAt p len w (len + 1)) (by simp [greedyAt_end hp hlt])
      (hT := by simp; omega)⟩

/-! ## The residues of a list -/

namespace Residues

/-- The local variables of residues: the arguments src, dst, m, dbl, len; the counter; the
residue. -/
registers [Src, Dst, Num, Dbl, Len, Idx, Res]

end Residues

open Residues in
/-- residues(src, dst, m, dbl, len).  The parameter pResid is the number of the procedure resid in
the program. -/
def residuesBody (pResid : ℕ) : Stmt :=
  .for Idx (v Num) (
    .call pResid [M (v Src +' v Idx), v Dbl, v Len] Res ;;
    .store (v Dst +' v Idx) (v Res))

/-- The time of residues. -/
def tResidues (m len : ℕ) : ℕ := m * (tResid len + 21) + 6

/-- What residues assumes: the table of the doubles of p stands at dbl, and the list l of m numbers
of absolute value at most U < 2^len at src; the m cells at dst lie in the memory and meet
neither. -/
structure ResiduesPre (lim : Limits) (μ : ℕ → ℤ) (src dst m dbl p len U : ℕ) (l : List ℤ) :
    Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  prime : 1 ≤ p
  segDbl : Seg μ dbl (dblList p len)
  segSrc : Seg μ src l
  length : l.length = m
  le : AbsLe l U
  lt : U < 2 ^ len
  spaceDbl : dbl + (len + 1) ≤ lim.space
  spaceSrc : src + m ≤ lim.space
  spaceDst : dst + m ≤ lim.space
  count : m < lim.space
  apartSrc : Apart dst m src m
  apartDbl : Apart dst m dbl (len + 1)
  word : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word

/-- The source array and doubles table are below the destination. -/
theorem ResiduesPre.of_array {μ : ℕ → ℤ} {src dst m dbl p len U : ℕ} {l : List ℤ}
    (h : ArrayAt μ src l m U dbl) (hdbl : Seg μ dbl (dblList p len))
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p) (hu : U < 2 ^ len)
    (hword : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word)
    (hlo : dbl + (len + 1) ≤ dst := by omega) (hhi : dst + m ≤ lim.space := by omega) :
    ResiduesPre lim μ src dst m dbl p len U l := by
  have hb := h.below
  exact ⟨hw, hp, hdbl, h.seg, h.len, h.bound, hu, by omega, by omega, hhi, by omega,
    Or.inr (by omega), Or.inr hlo, hword⟩

/-- The state of residues before round i: the first i residues are written, and no cell outside dst
has changed. -/
def ResiduesInv (μ : ℕ → ℤ) (src dst m dbl p len : ℕ) (l : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src, dst, m, dbl, len, i, r], μ'⟩ ∧
    SegN μ' dst (residList p (l.take i)) ∧ SameOutside μ μ' dst m

/-- One more residue. -/
theorem residList_take_succ (p : ℕ) {l : List ℤ} {i : ℕ} (hi : i < l.length) :
    residList p (l.take (i + 1)) = residList p (l.take i) ++ [resid p l[i]] := by
  rw [residList, residList, List.take_add_one, List.getElem?_eq_getElem hi, List.map_append]
  rfl

/-- **residues** writes the residues of a list and changes nothing else. -/
theorem residues_meets {μ : ℕ → ℤ} {q pResid src dst m dbl p len U : ℕ} {l : List ℤ}
    (hP : P[q]? = some (residuesBody pResid)) (hR : P[pResid]? = some residBody)
    (hd : d < lim.depth) (pre : ResiduesPre lim μ src dst m dbl p len U l) :
    Meets lim P q d [src, dst, m, dbl, len] μ (tResidues m len) fun _ μ' =>
      SegN μ' dst (residList p l) ∧ SameOutside μ μ' dst m := by
  refine .of_body hP ?_;
  obtain ⟨hw, hp, segDbl, segSrc, rfl, hle, hlt, spaceDbl, spaceSrc, spaceDst, hm, apartSrc,
    apartDbl, hword⟩ := pre
  have hltZ : (U : ℤ) < 2 ^ len := by exact_mod_cast hlt
  unfold tResidues
  -- for i < m
  refine Ends.for (ResiduesInv μ src dst l.length dbl p len l) l.length (tResid len + 13)
    ?start ?round ?done ?bound
  case start =>
    exact ⟨0, μ, congrArg (fun loc => (⟨loc, μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm), Seg.nil, .refl⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, seg, rest⟩
    have hread : μ' (src + i) = l[i] := (rest _ (by omega)).trans (segSrc.get hi)
    have hlen : (residList p (l.take i)).length = i := by simp [residList]; omega
    -- res := resid(src[i], dbl, len)
    light_call (resid_meets (w := l[i]) hR hw hp
      (segDbl.keep (by light_keep [length_dblList]))
      ((hle.getElem hi).trans_lt hltZ) spaceDbl hword) using hread with _ μ₁ ⟨rfl, rfl⟩
    -- dst[i] := res
    light_step
    refine ⟨by simp, resid p l[i],
      Function.update μ₁ (dst + i) (resid p l[i] : ℕ), by simp [update_frame_setLocal], ?_,
      rest.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := seg.snoc (resid p l[i])
    rwa [hlen, ← residList_take_succ p hi] at hsnoc
  case done =>
    rintro _ - ⟨r, μ', rfl, seg, rest⟩
    simp_all

end Light.Sec3
