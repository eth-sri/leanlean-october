/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Seg
import ThreeSumApsp.Lang.Tactics
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum

/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/


namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}
namespace Emod

/- The local variables of emod: the arguments x, M and fr (the result replaces x), what is left
of |x|, the number of entries of the table, and the next multiple of M. -/
slots Arg Modulus Free Rest Count Mult

end Emod

open Emod in
/-- One entry of the table: the multiple is written to the table and doubled. -/
def emodTableRound : Stmt :=
  .store (v Free +' v Count) (v Mult) ;;
  .set Count (v Count +' k 1) ;;
  .set Mult (v Mult +' v Mult)

open Emod in
/-- The table: M, 2M, 4M, … are written to the free pointer as long as they are at most |x|. -/
def emodTable : Stmt := .while (v Mult ≤' v Rest) emodTableRound

open Emod in
/-- The last entry of the table that has not been tried is subtracted if possible. -/
def emodReduceRound : Stmt :=
  .set Count (v Count -' k 1) ;;
  .ite (M (v Free +' v Count) ≤' v Rest) (.set Rest (v Rest -' M (v Free +' v Count))) .skip

open Emod in
/-- The entries of the table are subtracted, from the largest down, where possible. -/
def emodReduce : Stmt := .while (k 0 <' v Count) emodReduceRound

open Emod in
/-- The sign: the remainder r of |x| gives the remainder of x. -/
def emodSign : Stmt :=
  .ite (v Arg <' k 0)
    (.ite (v Rest =' k 0) (.set Arg (k 0)) (.set Arg (v Modulus -' v Rest)))
    (.set Arg (v Rest))

open Emod in
/-- emod(x, M, fr). -/
def emodBody : Stmt :=
  .ite (v Arg <' k 0) (.set Rest (k 0 -' v Arg)) (.set Rest (v Arg)) ;;
  .set Count (k 0) ;;
  .set Mult (v Modulus) ;;
  emodTable ;;
  emodReduce ;;
  emodSign

/-- The number of doublings: the least k with a < M 2^k. -/
def emodRounds (a M : ℕ) : ℕ := Nat.size (a / M)

/-- The time of emod, for a = |x|. -/
@[simp] def emodTime (a M : ℕ) : ℕ := 43 * emodRounds a M + 34

variable {M : ℕ}

/-- The multiple M 2^i is at most a exactly for i below the number of doublings. -/
theorem mul_two_pow_le_iff {a i : ℕ} (hM : 1 ≤ M) : M * 2 ^ i ≤ a ↔ i < emodRounds a M := by
  rw [emodRounds, Nat.lt_size, Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]

/-- There are at most log₂ (V + 1) + 1 doublings for a number up to V. -/
theorem emodRounds_le {a V : ℕ} (ha : a ≤ V) : emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by
  rw [emodRounds, Nat.size_le]
  calc a / M ≤ a := Nat.div_le_self _ _
    _ < V + 1 := by omega
    _ < 2 ^ (Nat.log 2 _ + 1) := by grind [Nat.lt_pow_succ_log_self]

/-- The remainder of a negative number. -/
theorem neg_emod_nat (a M : ℕ) (hM : 1 ≤ M) :
    (-(a : ℤ)) % (M : ℤ) = if a % M = 0 then 0 else (M : ℤ) - ((a % M : ℕ) : ℤ) := by
  have h : a = M * (a / M : ℕ) + ((a % M : ℕ) : ℤ) := by
    exact_mod_cast by grind [Nat.div_add_mod]
  have hlt : a % M < M := Nat.mod_lt _ (by omega)
  split_ifs with h0
  · rw [h0] at h
    rw [h, Nat.cast_zero, add_zero]
    simp
  · have e : -a = M - (a % M : ℕ) + M * (-((a / M : ℕ) : ℤ) - 1) := by
      linarith
    rw [e, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
namespace Emod

/-- What emod asks of the limits, for a modulus M ≥ 1, numbers up to V and the free pointer fr. -/
structure Pre (lim : Limits) (Mo V fr : ℕ) : Prop where
  mod_pos : 1 ≤ Mo
  space : (lim.space : ℤ) ≤ lim.word
  word : (4 * V + 4 * Mo + 16 : ℤ) ≤ lim.word
  free : fr + (Nat.log 2 (V + 1) + 2) ≤ lim.space

/-- The first i entries of the table are in place, and no cell below the free pointer has changed.
-/
def Table (μ μ' : ℕ → ℤ) (Mo fr i : ℕ) : Prop :=
  (∀ j < i, μ' (fr + j) = ((Mo * 2 ^ j : ℕ) : ℤ)) ∧ Kept μ μ' fr

variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}

/-- **The table.**  With K doublings, the K multiples M 2^j ≤ a are written. -/
theorem table_ends (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Ends lim P d emodTable ⟨frame [x, Mo, fr, a, 0, Mo], μ⟩ (19 * emodRounds a Mo + 6) fun σ' =>
      ∃ μ', σ' = ⟨frame [x, Mo, fr, a, emodRounds a Mo, ((Mo * 2 ^ emodRounds a Mo : ℕ) : ℤ)], μ'⟩ ∧
        Table μ μ' Mo fr (emodRounds a Mo) := by
  light_facts F
  have hK : emodRounds a Mo ≤ Nat.log 2 _ + 1 := emodRounds_le haV
  refine Ends.whileConst (fun i σ => ∃ μ',
    σ = ⟨frame [x, Mo, fr, a, i, (Mo * 2 ^ i : ℕ)], μ'⟩ ∧ Table μ μ' Mo fr i)
    (emodRounds a Mo) emodTableRound.blockCost ?start ?round ?done
    (by simp [emodTableRound]; omega)
  case start => exact ⟨μ, by simp, by omega, by tauto⟩
  case done =>
    rintro _ ⟨μ', rfl, tab⟩
    have hgt : ¬ Mo * 2 ^ emodRounds a Mo ≤ a := by grind [mul_two_pow_le_iff, lt_irrefl]
    generalize Mo * 2 ^ emodRounds a Mo = t at hgt
    exact ⟨by light_side, by simp; omega, μ', rfl, tab⟩
  case round =>
    rintro i _ hi ⟨μ', rfl, tab, below⟩
    have hle : Mo * 2 ^ i ≤ a := by simp_all [mul_two_pow_le_iff]
    have hnext : Mo * 2 ^ (i + 1) = Mo * 2 ^ i + Mo * 2 ^ i := by ring
    rw [hnext]
    generalize ht : Mo * 2 ^ i = t at hle
    refine ⟨by light_side, by simp; omega, ?_⟩
    unfold emodTableRound
    -- table[count] := mult; count := count + 1; mult := mult + mult
    light_store (fr + i) t
    light_set (i + 1)
    light_set (t + t)
    refine ⟨_, rfl, fun j hj => ?_, fun b hb => ?_⟩
    · grind
    · rw [Function.update_of_ne (by omega)]
      aesop

variable {μ' : ℕ → ℤ} {t : ℤ}

/-- **The subtractions.**  What is left of a after the multiples M 2^j have been subtracted, from
the largest down, where possible, is the remainder of a. -/
theorem reduce_ends (F : Pre lim Mo V fr) (haV : a ≤ V)     (tab : Table μ μ' Mo fr (emodRounds a Mo)) :
    Ends lim P d emodReduce ⟨frame [x, Mo, fr, a, emodRounds a Mo, t], μ'⟩
      (24 * emodRounds a Mo + 4) fun σ' => σ' = ⟨frame [x, Mo, fr, (a % Mo : ℕ), 0, t], μ'⟩ := by
  light_facts F
  have hK : emodRounds a Mo ≤ Nat.log 2 _ + 1 := emodRounds_le haV
  have hgt : a < Mo * 2 ^ emodRounds a Mo := by grind [not_le, mul_two_pow_le_iff, lt_irrefl]
  refine Ends.whileConst (fun i σ => ∃ r : ℕ,
    σ = ⟨frame [x, Mo, fr, r, (emodRounds a Mo - i : ℕ), t], μ'⟩ ∧
      r < Mo * 2 ^ (emodRounds a Mo - i) ∧ r % Mo = a % Mo) (emodRounds a Mo)
    emodReduceRound.blockCost ?start ?round ?done (by simp [emodReduceRound]; omega)
  case start => grind
  case done =>
    rintro _ ⟨r, rfl, hr, hmod⟩
    have hra : r = a % Mo := by grind [Nat.mod_eq_of_lt]
    exact ⟨by simp; omega, by simp, by simp_all⟩
  case round =>
    rintro i _ hi ⟨r, rfl, hr, hmod⟩
    obtain ⟨c, hc⟩ : ∃ c, emodRounds a Mo - i = c + 1 := by simp_all
    rw [show emodRounds a Mo - (i + 1) = c by omega]
    rw [hc] at hr ⊢
    have hcell := tab.1 c (by omega)
    have hle : Mo * 2 ^ c ≤ a := (mul_two_pow_le_iff F.mod_pos).2 (by omega)
    have hsub : ∀ r' : ℕ, Mo * 2 ^ c ≤ r' → (r' - Mo * 2 ^ c) % Mo = r' % Mo :=
      by grind [Nat.sub_mul_mod]
    rw [show Mo * 2 ^ (c + 1) = Mo * 2 ^ c + Mo * 2 ^ c by ring] at hr
    generalize Mo * 2 ^ c = m at hr hcell hle hsub ⊢
    refine ⟨by light_side, by light_side, ?_⟩
    unfold emodReduceRound
    -- count := count - 1; if table[count] ≤ rest then rest := rest - table[count]
    light_set c
    refine Ends.iteLast (fun h => ?_) fun h => ?_
    · have hmr : m ≤ r := by
        simp at h
        omega
      exact Ends.setTo _ ⟨r - m, rfl, by omega, by simp_all⟩
        (by light_side [hcell])
    · have hrm : r < m := by
        simp at h
        omega
      exact Ends.skip ⟨r, rfl, hrm, hmod⟩

/-- **The sign.** -/
theorem sign_ends (F : Pre lim Mo V fr) (hax : (a : ℤ) = |x|) :
    Ends lim P d emodSign ⟨frame [x, Mo, fr, (a % Mo : ℕ), 0, t], μ'⟩ 12 fun σ' =>
      σ'.loc 0 = x % (Mo : ℤ) ∧ σ'.mem = μ' := by
  have hword := F.word
  have hr : a % Mo < Mo := Nat.mod_lt _ F.mod_pos
  generalize hrem : a % Mo = r at hr
  refine Ends.iteLast (fun hneg => ?_) fun hpos => ?_
  · have hneg : x < 0 := by assumption
    have hmod := neg_emod_nat a Mo F.mod_pos
    rw [show -a = x by grind] at hmod
    refine Ends.iteLast (fun hz => ?_) fun hz => ?_
    · exact Ends.setTo 0 ⟨by simp_all, rfl⟩
    · exact Ends.setTo (Mo - r) ⟨by simp_all, rfl⟩
  · have hpos : 0 ≤ x := by simp_all
    refine Ends.setTo r ⟨?_, rfl⟩
    rw [← abs_of_nonneg hpos, ← hax, ← hrem]
    rfl

/-- **emod(x, M, fr)** returns the remainder of x modulo M and changes no cell below the free
pointer. -/
theorem _root_.Light.emod_meets {p : ℕ} (hp : P[p]? = some emodBody) (F : Pre lim Mo V fr)
    (hx : |x| ≤ (V : ℤ)) :
    Meets lim P p d [x, Mo, fr] μ (emodTime x.natAbs Mo) fun r μ' =>
      r = x % (Mo : ℤ) ∧ Kept μ μ' fr := by
  have hword := F.word
  have hax := x.natCast_natAbs
  have haV : x.natAbs ≤ V := by omega
  refine .of_body hp ?_
  generalize x.natAbs = a at hax haV ⊢
  -- count := 0; mult := M; the table; the subtractions; the sign
  have tail : Ends lim P d (.set Count (k 0) ;; .set Mult (v Modulus) ;; emodTable ;;
      emodReduce ;; emodSign) ⟨frame [x, Mo, fr, a], μ⟩ (43 * emodRounds a Mo + 26) fun σ' =>
      σ'.loc 0 = x % Mo ∧ Kept μ σ'.mem fr := by
    refine Ends.setToThen 0 (Ends.setToThen Mo ?_)
    refine Ends.next _ ((table_ends F haV).mono le_rfl ?_)
    rintro _ ⟨μ', rfl, tab⟩
    refine Ends.next _ ((reduce_ends F haV tab).mono le_rfl ?_)
    rintro _ rfl
    exact (sign_ends F hax).mono (by light_time) fun σ' h =>
      ⟨h.1, fun b hb => by rw [h.2]; exact tab.2 b hb⟩
  -- rest := |x|
  refine Ends.iteThen (fun hneg => ?_) fun hpos => ?_
  · have hneg : x < 0 := by assumption
    rw [abs_of_neg hneg] at hax
    exact Ends.setToThen a (by simp_all)
  · have hpos : 0 ≤ x := by simp_all
    rw [abs_of_nonneg hpos] at hax
    exact Ends.setToThen a (tail.mono (by light_time) fun _ h => h)
