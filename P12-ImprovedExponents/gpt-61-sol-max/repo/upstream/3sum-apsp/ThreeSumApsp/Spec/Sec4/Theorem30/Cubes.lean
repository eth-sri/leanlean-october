/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Sec4.Boxes
public import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays

/-!
# Cubes, leaves and output strings as lists of digits (Sections 4.2 and 4.3)

A term has the digit P_ij ↦ 3(i - 1) + (j - 1), P₀ ↦ 9, and an output variable the digit
z_ij ↦ 3(i - 1) + (j - 1), z₀ ↦ 9.  A symbol of a cube that is a term keeps the digit of the term,
and the star has the digit 10.  A cube, a leaf or an output string is handled as the list of its L
digits, level 1 first: `digitsC` for cubes, `digitsT` for strings of terms (leaves), `digitsO` for
output strings.  This file translates the notions of Sections 4.2 and 4.3 into operations on such
lists:

* the inner set of an output string η (the paper's w) is the positions of its digit 9, the stars of
  π are the positions of 10, the symbols P₀ of τ the positions of 9, and their numbers are counts
  (`card_innerSetO`, `card_starLevels`, `card_P0Levels`);
* "replacing its e lowest symbols P₀ […] by stars" is `starFirst` (`digitsC_starLowest`);
* "replacing its stars with P₀" is `starsToNines` (`digitsT_starsToP0`);
* "the highest level at which π has a star" is `lastStar` (`lastStar_digitsC`), and π[ℓ ← λ] is
  `List.set` (`digitsC_replace`);
* the dynamic program of Lemma 29 is `dpValueD` (`dpValueD_digitsC`): the product `leafProduct` for
  a list without stars, and the step `sumAtLastStar`; `storedD` is what it computes for a box, at
  the number of stars of the box.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Cubes, leaves and output strings -/

/-- The digit of a symbol of a cube: a term keeps its digit, the star has 10. -/
def cubeIdx : CubeSymbol → Fin 11
  | .term lam => ⟨termIdx lam, by omega⟩
  | .star => 10

/-- The symbol with a given digit. -/
def cubeOfIdx (k : Fin 11) : CubeSymbol :=
  if h : (k : ℕ) < 10 then .term (termOfIdx ⟨k, h⟩) else .star

/-- The symbols of cubes and their digits. -/
def cubeEquiv : CubeSymbol ≃ Fin 11 where
  toFun := cubeIdx
  invFun := cubeOfIdx
  left_inv := by
    decide
  right_inv := by
    decide

/-- The digits of a cube, level 1 first. -/
def digitsC {L : ℕ} (π : Cube L) := digitsStr cubeEquiv π
/-- The digits of a leaf, level 1 first. -/
def digitsT {L : ℕ} (τ : Leaf L) := digitsStr termEquiv τ
/-- The digits of an output string, level 1 first. -/
def digitsO {L : ℕ} (η : OutStr L) := digitsStr outEquiv η

section

variable {L : ℕ} (π : Cube L) (τ : Leaf L) (η : OutStr L)

theorem length_digitsC : (digitsC π).length = L := length_digitsStr _ π
theorem length_digitsT : (digitsT τ).length = L := length_digitsStr _ τ
theorem length_digitsO : (digitsO η).length = L := length_digitsStr _ η

theorem digitsC_lt : ∀ d ∈ digitsC π, d < 11 := digitsStr_lt _ π
theorem digitsT_lt : ∀ d ∈ digitsT τ, d < 10 := digitsStr_lt _ τ
theorem digitsO_lt : ∀ d ∈ digitsO η, d < 10 := digitsStr_lt _ η

variable (ℓ : Fin L)

include ℓ in
private theorem getD_digitsC  : (digitsC π).getD ℓ 0 = cubeIdx (π ℓ) :=
  getD_digitsStr _ π ℓ
include ℓ in
theorem getD_digitsT  : (digitsT τ).getD ℓ 0 = termIdx (τ ℓ) := getD_digitsStr _ τ ℓ
include ℓ in
theorem getD_digitsO  : (digitsO η).getD ℓ 0 = outIdx (η ℓ) := getD_digitsStr _ η ℓ

/-- A list with L members and the right digit at every level is the list of digits of the cube. -/
def digitsC_eq_of_getD {l : List ℕ} (hl : l.length = L)
    (h : ∀ ℓ : Fin L, l.getD ℓ 0 = cubeIdx (π ℓ)) :=
  digitsStr_eq_of_getD cubeEquiv π hl h

theorem ofDigitList_digitsT : ofDigitList 10 (digitsT τ) = codeT τ := ofDigitList_digitsStr _ τ
theorem ofDigitList_digitsO : ofDigitList 10 (digitsO η) = codeO η := ofDigitList_digitsStr _ η

end

theorem digitsC_injective L : Function.Injective (digitsC : Cube L → List ℕ) :=
  digitsStr_injective _
theorem digitsT_injective L : Function.Injective (digitsT : Leaf L → List ℕ) :=
  digitsStr_injective _

/-- Every list of L digits below 10 is the list of digits of a leaf. -/
theorem exists_digitsT {L} l (hl : l.length = L) (hd : ∀ d ∈ l, d < 10) :
    ∃ τ : Leaf L, digitsT τ = l := exists_digitsStr _ l hl hd

/-! ## The levels of a symbol are the positions of its digit -/

/-- The number of stars in a list of digits: the star has the digit 10. -/
abbrev starCount (l : List ℕ) := l.count 10

private theorem cubeIdx_star : (cubeIdx .star : ℕ) = 10 := rfl

theorem cubeIdx_term lam : (cubeIdx (.term lam) : ℕ) = termIdx lam := rfl

/-- The star is the only symbol with the digit 10. -/
private theorem cubeIdx_eq_ten s : (cubeIdx s : ℕ) = 10 ↔ s = .star := by
  ram_grind [cubeIdx]

/-- P₀ is the only term with the digit 9. -/
theorem termIdx_eq_nine lam : (termIdx lam : ℕ) = 9 ↔ lam = .P0 := by
  ram_grind [termIdx]

section

variable {L : ℕ} (π : Cube L) (τ : Leaf L) (η : OutStr L)

/-- The levels of the inner set are the positions of the digit 9. -/
theorem getD_digitsO_eq_nine (ℓ : Fin L) : (digitsO η).getD ℓ 0 = 9 ↔ ℓ ∈ innerSetO η := by
  rw [getD_digitsO, innerSetO, Finset.mem_filter_univ, outVar_isInner_iff]

/-- A statement on all positions of the digit 9 is a statement on all levels of the inner set. -/
theorem forall_nine_digitsO (P : ℕ → Prop) :
    (∀ j, (digitsO η).getD j 0 = 9 → P j) ↔ ∀ ℓ ∈ innerSetO η, P ℓ :=
  (forall_getD_digitsStr outEquiv η (by norm_num) P).trans <| forall_congr' fun ℓ => by
    rw [← getD_digitsO_eq_nine, getD_digitsO]
    rfl

/-- A statement on all positions of the digit 10 is a statement on all levels with a star. -/
private theorem forall_ten_digitsC (P : ℕ → Prop) :
    (∀ j, (digitsC π).getD j 0 = 10 → P j) ↔ ∀ ℓ ∈ Cube.starLevels π, P ℓ :=
  (forall_getD_digitsStr cubeEquiv π (by norm_num) P).trans <| forall_congr' fun ℓ => by
    rw [Cube.starLevels, Finset.mem_filter_univ, ← cubeIdx_eq_ten]
    rfl

/-- The size of the inner set is the number of digits 9. -/
theorem card_innerSetO : (innerSetO η).card = (digitsO η).count 9 := by
  rw [digitsO, digitsStr, List.count_ofFn]
  exact congrArg Finset.card (Finset.filter_congr fun ℓ _ => outVar_isInner_iff (η ℓ))

/-- The number of stars is the number of digits 10. -/
theorem card_starLevels : (Cube.starLevels π).card = starCount (digitsC π) := by
  rw [starCount, digitsC, digitsStr, List.count_ofFn]
  exact congrArg Finset.card (Finset.filter_congr fun ℓ _ => (cubeIdx_eq_ten (π ℓ)).symm)

/-- The number of symbols P₀ is the number of digits 9. -/
theorem card_P0Levels : (P0Levels τ).card = (digitsT τ).count 9 := by
  rw [digitsT, digitsStr, List.count_ofFn]
  exact congrArg Finset.card (Finset.filter_congr fun ℓ _ => (termIdx_eq_nine (τ ℓ)).symm)

end

/-! ## The lowest symbols P₀ turned into stars -/

/-- The first e digits 9 turned into 10 (Section 4.2: "replacing its e lowest symbols P₀ […] by
stars"). -/
def starFirst
  | 0, l => l
  | _ + 1, [] => []
  | e + 1, d :: l => if d = 9 then 10 :: starFirst e l else d :: starFirst (e + 1) l

theorem starFirst_zero l : starFirst 0 l = l := by
  cases l <;> rfl

theorem length_starFirst e l : (starFirst e l).length = l.length := by
  fun_induction starFirst e l <;> simp_all

/-- The digits of `starFirst e l`: a digit 9 with fewer than e digits 9 before it becomes 10. -/
theorem getD_starFirst e l i :
    (starFirst e l).getD i 0
      = if l.getD i 0 = 9 ∧ (l.take i).count 9 < e then 10 else l.getD i 0 := by
  fun_induction starFirst e l generalizing i <;> cases i <;> simp_all

/-- Replacing the e lowest symbols P₀ of a leaf by stars is `starFirst e` on its digits. -/
theorem digitsC_starLowest {L} e (τ : Leaf L) :
    digitsC (starLowest e τ) = starFirst e (digitsT τ) := by
  refine digitsC_eq_of_getD _ (by rw [length_starFirst, length_digitsT]) fun ℓ => ?_

  have  : ℓ ∈ lowest e (P0Levels τ) ↔
      (digitsT τ).getD ℓ 0 = 9 ∧ ((digitsT τ).take ℓ).count 9 < e := by
    rw [(by
      rw [digitsT, digitsStr, List.count_take_ofFn]
      refine congrArg Finset.card (Finset.ext fun ℓ' => ?_)
      rw [Finset.mem_filter_univ, Finset.mem_filter, P0Levels, Finset.mem_filter_univ, Fin.lt_def,
        and_comm]
      exact and_congr_left' (termIdx_eq_nine (τ ℓ'))
     : ((digitsT τ).take ℓ).count 9 = ((P0Levels τ).filter fun ℓ' => ℓ' < ℓ).card), getD_digitsT, termIdx_eq_nine, lowest, Finset.mem_filter, P0Levels,
      Finset.mem_filter_univ]
  rw [getD_starFirst, starLowest, Cube.starAt]
  grind [cubeIdx_star, getD_digitsT, cubeIdx_term]

/-! ## Stars turned into P₀, and a symbol replaced by a term -/

/-- Stars turned into P₀ (proof of Lemma 29). -/
def starsToNines (l : List ℕ) := l.map fun d => if d = 10 then 9 else d

/-- A list without the digit 10 is not changed. -/
theorem starsToNines_of_notMem {s} (h : 10 ∉ s) : starsToNines s = s := by
  rw [starsToNines]
  conv_rhs => rw [← List.map_id s]
  exact List.map_congr_left fun d hd => if_neg fun h' : d = 10 => h (h' ▸ hd)

/-- Turning the stars back into nines undoes `starFirst`. -/
theorem starsToNines_starFirst e {l} (h : 10 ∉ l) :
    starsToNines (starFirst e l) = l := by
  fun_induction starFirst e l with
  | case1 l => exact starsToNines_of_notMem h
  | case2 => rfl
  | case3 e l ih => simp_all [starsToNines]
  | case4 e d l hd ih =>
    ram_arith [starsToNines]

/-- Replacing the stars of a cube with P₀ is `starsToNines` on its digits. -/
private theorem digitsT_starsToP0 {L} (π : Cube L) :
    digitsT (Cube.starsToP0 π) = starsToNines (digitsC π) := by
  rw [digitsT, starsToNines, digitsC, digitsStr, digitsStr, List.map_ofFn]
  refine congrArg List.ofFn (funext fun ℓ => ?_)
  simp only [Cube.starsToP0, Function.comp]
  cases π ℓ with
  | term lam => exact (if_neg (Nat.ne_of_lt (termIdx lam).isLt)).symm
  | star => rfl

/-- π[ℓ ← λ] (the proof of Lemma 29) on digits: the digit at position ℓ is set to the digit of λ. -/
theorem digitsC_replace {L} π (ℓ : Fin L) lam :
    digitsC (Cube.replace π ℓ lam) = (digitsC π).set ℓ (termIdx lam) := by
  refine digitsC_eq_of_getD _ (by rw [List.length_set, length_digitsC]) fun i => ?_
  rw [Cube.replace, List.getD_eq_getElem?_getD]
  by_cases h : i = ℓ
  · simp_all [length_digitsC, cubeIdx_term]
  · rw [Function.update_of_ne h, List.getElem?_set_ne fun hℓi => h (Fin.ext hℓi.symm),
      ← List.getD_eq_getElem?_getD, getD_digitsC]

/-! ## The highest star -/

/-- The position of the last digit 10, if there is one (proof of Lemma 29: "the highest level at
which π has a star"). -/
def lastStar
  | [] => none
  | d :: l =>
    match lastStar l with
    | some p => some (p + 1)
    | none => if d = 10 then some 0 else none

/-- `lastStar` finds nothing exactly if the digit 10 does not occur. -/
private theorem lastStar_eq_none_iff l : lastStar l = none ↔ ∀ j, l.getD j 0 ≠ 10 := by
  induction l with
  | nil => simp [lastStar]
  | cons d l ih =>
    rw [← Nat.and_forall_add_one, lastStar]
    simp only [List.getD_cons_zero, List.getD_cons_succ, ← ih]
    cases lastStar l <;> simp

/-- `lastStar` finds the last position of the digit 10. -/
theorem lastStar_eq_some_iff l p :
    lastStar l = some p ↔ l.getD p 0 = 10 ∧ ∀ j, p < j → l.getD j 0 ≠ 10 := by
  induction l generalizing p with
  | nil => simp [lastStar]
  | cons d l ih =>
    rw [← Nat.and_forall_add_one, lastStar]
    cases p with
    | zero =>
      simp only [List.getD_cons_zero, List.getD_cons_succ, lt_irrefl, false_imp_iff, true_and,
        Nat.zero_lt_succ, forall_true_left, ← lastStar_eq_none_iff]
      cases lastStar l <;> simp
    | succ p =>
      ram_safe

/-- On the digits of a cube with a star, `lastStar` finds the highest level at which it has a
star. -/
theorem lastStar_digitsC {L} (π : Cube L) (h : (Cube.starLevels π).Nonempty) :
    lastStar (digitsC π) = some ((Cube.starLevels π).max' h : ℕ) := by

  refine (lastStar_eq_some_iff _ _).mpr ⟨?_, fun j hj h10 => ((forall_ten_digitsC π fun j => ¬ (Cube.starLevels π).max' h < j).mpr
    fun ℓ hℓ => not_lt.mpr (Fin.le_def.mp (Finset.le_max' _ _ hℓ))
  ) j h10 hj⟩
  rw [getD_digitsC, cubeIdx_eq_ten]
  simpa [Cube.starLevels] using Finset.max'_mem _ h

/-- `lastStar` finds nothing exactly if the cube has no star. -/
private theorem lastStar_digitsC_eq_none_iff {L} (π : Cube L) :
    lastStar (digitsC π) = none ↔ Cube.starLevels π = ∅ := by
  rw [lastStar_eq_none_iff, Finset.eq_empty_iff_forall_notMem]
  exact forall_ten_digitsC π _

/-! ## The dynamic program of Lemma 29 on digits -/

/-- The product of the two numbers that the encodings have for the leaf with the digits l; the
encodings are arrays indexed by the codes of the leaves. -/
def leafProduct (encA encB : List ℤ) (l : List ℕ) :=
  encA.getD (ofDigitList 10 l) 0 * encB.getD (ofDigitList 10 l) 0

/-- The values val(π[ℓ ← λ]) for the ten terms λ, in the order of their digits; l is the list of
digits of π, and p is the position ℓ. -/
def tenValues (val : List ℕ → ℤ) (l : List ℕ) (p : ℕ) :=
  (List.range 10).map fun d => val (l.set p d)

/-- The step of the dynamic program of Lemma 29: the sum ∑_λ val(π[ℓ ← λ]), where ℓ is "the highest
level at which π has a star".  For a list without a star it is 0. -/
def sumAtLastStar (val : List ℕ → ℤ) (l : List ℕ) :=
  match lastStar l with
  | some p => (tenValues val l p).sum
  | none => 0

/-- The step of the dynamic program uses only the ten values that it adds up. -/
theorem sumAtLastStar_congr {val val'} {l} {p} (hp : lastStar l = some p)
    (h : ∀ d < 10, val (l.set p d) = val' (l.set p d)) :
    sumAtLastStar val l = sumAtLastStar val' l := by
  rw [sumAtLastStar, sumAtLastStar, hp]
  exact congrArg List.sum (List.map_congr_left fun d hd => h d (List.mem_range.mp hd))

/-- The dynamic program of Lemma 29 on lists of digits; e is the number of stars. -/
def dpValueD (encA encB : List ℤ)
  | 0, l => leafProduct encA encB (starsToNines l)
  | e + 1, l => sumAtLastStar (dpValueD encA encB e) l

/-- The value that is stored for the box l: what the dynamic program of Lemma 29 computes for it, at
its number of stars. -/
def storedD (encA encB : List ℤ) (l : List ℕ) := dpValueD encA encB (starCount l) l

/-- On the arrays of two encodings, the product at the digits of a leaf is the product of its two
numbers. -/
theorem leafProduct_digitsT {L} encA encB (τ : Leaf L) :
    leafProduct (arrT encA) (arrT encB) (digitsT τ) = encA τ * encB τ := by
  grind [ofDigitList_digitsT, leafProduct, getD_arrT]

/-- The dynamic program on digits, run on the arrays of the two encodings, is the dynamic program
of Lemma 29. -/
theorem dpValueD_digitsC {L} encA encB e (π : Cube L) :
    dpValueD (arrT encA) (arrT encB) e (digitsC π) = dpValue encA encB e π := by
  induction e generalizing π with
  | zero => rw [dpValueD, dpValue, ← digitsT_starsToP0, leafProduct_digitsT]
  | succ e ih =>
    rw [dpValueD, dpValue, sumAtLastStar]
    by_cases h : (Cube.starLevels π).Nonempty
    · rw [dif_pos h, lastStar_digitsC π h]
      -- a star is found: the sum of ten values
      simp only [tenValues]
      rw [List.sum_map_range, ← Fin.sum_univ_eq_sum_range, ← termEquiv.sum_comp]
      refine Finset.sum_congr rfl fun lam _ => ?_
      rw [← ih, digitsC_replace]
      rfl
    · grind [lastStar_digitsC_eq_none_iff]

end ThreeSumApsp.Spec
