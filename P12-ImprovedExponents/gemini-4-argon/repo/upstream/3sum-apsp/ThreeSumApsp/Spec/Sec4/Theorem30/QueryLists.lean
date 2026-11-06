module

public import ThreeSumApsp.Sec4.Boxes
public import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.List.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ThreeSumApsp.Sec4.Corollary31

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Cubes, leaves and output strings -/

/-- The digit of a symbol of a cube: a term keeps its digit, the star has 10. -/
def cubeIdx : CubeSymbol → Fin 11
  | .term lam => ⟨termIdx lam, by have := (termIdx lam).isLt; omega⟩
  | .star => 10

/-- The symbol with a given digit. -/
def cubeOfIdx (k : Fin 11) : CubeSymbol :=
  if h : (k : ℕ) < 10 then .term (termOfIdx ⟨k, h⟩) else .star

/-- The symbols of cubes and their digits. -/
def cubeEquiv : CubeSymbol ≃ Fin 11 where
  toFun := cubeIdx
  invFun := cubeOfIdx
  left_inv := by
    intro s
    cases s with
    | term lam =>
      cases lam with
      | P i j => fin_cases i <;> fin_cases j <;> rfl
      | P0 => rfl
    | star => rfl
  right_inv := by
    intro k
    fin_cases k <;> rfl

/-- The digits of a cube, level 1 first. -/
def digitsC {L : ℕ} (π : Cube L) : List ℕ := digitsStr cubeEquiv π
/-- The digits of a leaf, level 1 first. -/
def digitsT {L : ℕ} (τ : Leaf L) : List ℕ := digitsStr termEquiv τ
/-- The digits of an output string, level 1 first. -/
def digitsO {L : ℕ} (η : OutStr L) : List ℕ := digitsStr outEquiv η

section

variable {L : ℕ} (π : Cube L) (τ : Leaf L) (η : OutStr L)

theorem length_digitsC : (digitsC π).length = L := length_digitsStr _ π
theorem length_digitsT : (digitsT τ).length = L := length_digitsStr _ τ
theorem length_digitsO : (digitsO η).length = L := length_digitsStr _ η

theorem digitsC_lt : ∀ d ∈ digitsC π, d < 11 := digitsStr_lt _ π
theorem digitsT_lt : ∀ d ∈ digitsT τ, d < 10 := digitsStr_lt _ τ
theorem digitsO_lt : ∀ d ∈ digitsO η, d < 10 := digitsStr_lt _ η

theorem getD_digitsC (ℓ : Fin L) : (digitsC π).getD ℓ 0 = cubeIdx (π ℓ) :=
  getD_digitsStr _ π ℓ
theorem getD_digitsT (ℓ : Fin L) : (digitsT τ).getD ℓ 0 = termIdx (τ ℓ) := getD_digitsStr _ τ ℓ
theorem getD_digitsO (ℓ : Fin L) : (digitsO η).getD ℓ 0 = outIdx (η ℓ) := getD_digitsStr _ η ℓ

/-- A list with L members and the right digit at every level is the list of digits of the cube. -/
theorem digitsC_eq_of_getD {l : List ℕ} (hl : l.length = L)
    (h : ∀ ℓ : Fin L, l.getD ℓ 0 = cubeIdx (π ℓ)) : digitsC π = l :=
  digitsStr_eq_of_getD cubeEquiv π hl h

theorem ofDigitList_digitsT : ofDigitList 10 (digitsT τ) = codeT τ := ofDigitList_digitsStr _ τ
theorem ofDigitList_digitsO : ofDigitList 10 (digitsO η) = codeO η := ofDigitList_digitsStr _ η

end

theorem digitsC_injective (L : ℕ) : Function.Injective (digitsC : Cube L → List ℕ) :=
  digitsStr_injective _
theorem digitsT_injective (L : ℕ) : Function.Injective (digitsT : Leaf L → List ℕ) :=
  digitsStr_injective _

/-- Every list of L digits below 10 is the list of digits of a leaf. -/
theorem exists_digitsT {L : ℕ} (l : List ℕ) (hl : l.length = L) (hd : ∀ d ∈ l, d < 10) :
    ∃ τ : Leaf L, digitsT τ = l := exists_digitsStr _ l hl hd

/-! ## The levels of a symbol are the positions of its digit -/

/-- The number of stars in a list of digits: the star has the digit 10. -/
abbrev starCount (l : List ℕ) : ℕ := l.count 10

theorem cubeIdx_star : (cubeIdx .star : ℕ) = 10 := rfl

theorem cubeIdx_term (lam : Term) : (cubeIdx (.term lam) : ℕ) = termIdx lam := rfl

/-- The star is the only symbol with the digit 10. -/
theorem cubeIdx_eq_ten (s : CubeSymbol) : (cubeIdx s : ℕ) = 10 ↔ s = .star := by
  cases s with
  | term lam =>
    have := (termIdx lam).isLt
    simp only [cubeIdx, reduceCtorEq, iff_false]
    omega
  | star => simp [cubeIdx]

/-- P₀ is the only term with the digit 9. -/
theorem termIdx_eq_nine (lam : Term) : (termIdx lam : ℕ) = 9 ↔ lam = .P0 := by
  cases lam with
  | P i j =>
    simp only [termIdx, reduceCtorEq, iff_false]
    omega
  | P0 => simp [termIdx]

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
theorem forall_ten_digitsC (P : ℕ → Prop) :
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
def starFirst : ℕ → List ℕ → List ℕ
  | 0, l => l
  | _ + 1, [] => []
  | e + 1, d :: l => if d = 9 then 10 :: starFirst e l else d :: starFirst (e + 1) l

theorem starFirst_zero (l : List ℕ) : starFirst 0 l = l := by
  cases l <;> rfl

theorem length_starFirst (e : ℕ) (l : List ℕ) : (starFirst e l).length = l.length := by
  fun_induction starFirst e l <;> simp_all

/-- The digits of `starFirst e l`: a digit 9 with fewer than e digits 9 before it becomes 10. -/
theorem getD_starFirst (e : ℕ) (l : List ℕ) (i : ℕ) :
    (starFirst e l).getD i 0
      = if l.getD i 0 = 9 ∧ (l.take i).count 9 < e then 10 else l.getD i 0 := by
  fun_induction starFirst e l generalizing i <;> cases i <;> simp_all

/-- Replacing the e lowest symbols P₀ of a leaf by stars is `starFirst e` on its digits. -/
theorem digitsC_starLowest {L : ℕ} (e : ℕ) (τ : Leaf L) :
    digitsC (starLowest e τ) = starFirst e (digitsT τ) := by
  refine digitsC_eq_of_getD _ (by rw [length_starFirst, length_digitsT]) fun ℓ => ?_
  have hcount : ((digitsT τ).take ℓ).count 9 = ((P0Levels τ).filter fun ℓ' => ℓ' < ℓ).card := by
    rw [digitsT, digitsStr, List.count_take_ofFn]
    refine congrArg Finset.card (Finset.ext fun ℓ' => ?_)
    rw [Finset.mem_filter_univ, Finset.mem_filter, P0Levels, Finset.mem_filter_univ, Fin.lt_def,
      and_comm]
    exact and_congr_left' (termIdx_eq_nine (τ ℓ'))
  have hmem : ℓ ∈ lowest e (P0Levels τ) ↔
      (digitsT τ).getD ℓ 0 = 9 ∧ ((digitsT τ).take ℓ).count 9 < e := by
    rw [hcount, getD_digitsT, termIdx_eq_nine, lowest, Finset.mem_filter, P0Levels,
      Finset.mem_filter_univ]
  rw [getD_starFirst, starLowest, Cube.starAt]
  by_cases hc : ℓ ∈ lowest e (P0Levels τ)
  · rw [if_pos hc, if_pos (hmem.mp hc), cubeIdx_star]
  · rw [if_neg hc, if_neg fun h => hc (hmem.mpr h), getD_digitsT, cubeIdx_term]

/-! ## Stars turned into P₀, and a symbol replaced by a term -/

/-- Stars turned into P₀ (proof of Lemma 29). -/
def starsToNines (l : List ℕ) : List ℕ := l.map fun d => if d = 10 then 9 else d

/-- A list without the digit 10 is not changed. -/
theorem starsToNines_of_notMem {s : List ℕ} (h : 10 ∉ s) : starsToNines s = s := by
  rw [starsToNines]
  conv_rhs => rw [← List.map_id s]
  exact List.map_congr_left fun d hd => if_neg fun h' : d = 10 => h (h' ▸ hd)

/-- Turning the stars back into nines undoes `starFirst`. -/
theorem starsToNines_starFirst (e : ℕ) {l : List ℕ} (h : 10 ∉ l) :
    starsToNines (starFirst e l) = l := by
  fun_induction starFirst e l with
  | case1 l => exact starsToNines_of_notMem h
  | case2 => rfl
  | case3 e l ih => simp_all [starsToNines]
  | case4 e d l hd ih =>
    rw [starsToNines, List.map_cons, if_neg fun h10 : d = 10 => h (h10 ▸ List.mem_cons_self)]
    exact congrArg (d :: ·) (ih fun h' => h (List.mem_cons_of_mem _ h'))

/-- Replacing the stars of a cube with P₀ is `starsToNines` on its digits. -/
theorem digitsT_starsToP0 {L : ℕ} (π : Cube L) :
    digitsT (Cube.starsToP0 π) = starsToNines (digitsC π) := by
  rw [digitsT, starsToNines, digitsC, digitsStr, digitsStr, List.map_ofFn]
  refine congrArg List.ofFn (funext fun ℓ => ?_)
  simp only [Cube.starsToP0, Function.comp]
  cases π ℓ with
  | term lam => exact (if_neg (Nat.ne_of_lt (termIdx lam).isLt)).symm
  | star => rfl

/-- π[ℓ ← λ] (the proof of Lemma 29) on digits: the digit at position ℓ is set to the digit of λ. -/
theorem digitsC_replace {L : ℕ} (π : Cube L) (ℓ : Fin L) (lam : Term) :
    digitsC (Cube.replace π ℓ lam) = (digitsC π).set ℓ (termIdx lam) := by
  refine digitsC_eq_of_getD _ (by rw [List.length_set, length_digitsC]) fun i => ?_
  rw [Cube.replace, List.getD_eq_getElem?_getD]
  by_cases h : i = ℓ
  · rw [h, Function.update_self, List.getElem?_set_self (by rw [length_digitsC]; exact ℓ.isLt),
      cubeIdx_term, Option.getD_some]
  · rw [Function.update_of_ne h, List.getElem?_set_ne fun hℓi => h (Fin.ext hℓi.symm),
      ← List.getD_eq_getElem?_getD, getD_digitsC]

/-! ## The highest star -/

/-- The position of the last digit 10, if there is one (proof of Lemma 29: "the highest level at
which π has a star"). -/
def lastStar : List ℕ → Option ℕ
  | [] => none
  | d :: l =>
    match lastStar l with
    | some p => some (p + 1)
    | none => if d = 10 then some 0 else none

/-- `lastStar` finds nothing exactly if the digit 10 does not occur. -/
theorem lastStar_eq_none_iff (l : List ℕ) : lastStar l = none ↔ ∀ j, l.getD j 0 ≠ 10 := by
  induction l with
  | nil => simp [lastStar]
  | cons d l ih =>
    rw [← Nat.and_forall_add_one, lastStar]
    simp only [List.getD_cons_zero, List.getD_cons_succ, ← ih]
    cases lastStar l <;> simp

/-- `lastStar` finds the last position of the digit 10. -/
theorem lastStar_eq_some_iff (l : List ℕ) (p : ℕ) :
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
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.not_lt_zero, false_imp_iff,
        true_and, Nat.add_lt_add_iff_right, ← ih]
      cases lastStar l <;> simp

/-- On the digits of a cube with a star, `lastStar` finds the highest level at which it has a
star. -/
theorem lastStar_digitsC {L : ℕ} (π : Cube L) (h : (Cube.starLevels π).Nonempty) :
    lastStar (digitsC π) = some ((Cube.starLevels π).max' h : ℕ) := by
  have hmax := (forall_ten_digitsC π fun j => ¬ ((Cube.starLevels π).max' h : ℕ) < j).mpr
    fun ℓ hℓ => not_lt.mpr (Fin.le_def.mp (Finset.le_max' _ _ hℓ))
  refine (lastStar_eq_some_iff _ _).mpr ⟨?_, fun j hj h10 => hmax j h10 hj⟩
  rw [getD_digitsC, cubeIdx_eq_ten]
  simpa [Cube.starLevels] using Finset.max'_mem _ h

/-- `lastStar` finds nothing exactly if the cube has no star. -/
theorem lastStar_digitsC_eq_none_iff {L : ℕ} (π : Cube L) :
    lastStar (digitsC π) = none ↔ Cube.starLevels π = ∅ := by
  rw [lastStar_eq_none_iff, Finset.eq_empty_iff_forall_notMem]
  exact forall_ten_digitsC π fun _ => False

/-! ## The dynamic program of Lemma 29 on digits -/

/-- The product of the two numbers that the encodings have for the leaf with the digits l; the
encodings are arrays indexed by the codes of the leaves. -/
def leafProduct (encA encB : List ℤ) (l : List ℕ) : ℤ :=
  encA.getD (ofDigitList 10 l) 0 * encB.getD (ofDigitList 10 l) 0

/-- The values val(π[ℓ ← λ]) for the ten terms λ, in the order of their digits; l is the list of
digits of π, and p is the position ℓ. -/
def tenValues (val : List ℕ → ℤ) (l : List ℕ) (p : ℕ) : List ℤ :=
  (List.range 10).map fun d => val (l.set p d)

/-- The step of the dynamic program of Lemma 29: the sum ∑_λ val(π[ℓ ← λ]), where ℓ is "the highest
level at which π has a star".  For a list without a star it is 0. -/
def sumAtLastStar (val : List ℕ → ℤ) (l : List ℕ) : ℤ :=
  match lastStar l with
  | some p => (tenValues val l p).sum
  | none => 0

/-- The step of the dynamic program uses only the ten values that it adds up. -/
theorem sumAtLastStar_congr {val val' : List ℕ → ℤ} {l : List ℕ} {p : ℕ} (hp : lastStar l = some p)
    (h : ∀ d < 10, val (l.set p d) = val' (l.set p d)) :
    sumAtLastStar val l = sumAtLastStar val' l := by
  rw [sumAtLastStar, sumAtLastStar, hp]
  exact congrArg List.sum (List.map_congr_left fun d hd => h d (List.mem_range.mp hd))

/-- The dynamic program of Lemma 29 on lists of digits; e is the number of stars. -/
def dpValueD (encA encB : List ℤ) : ℕ → List ℕ → ℤ
  | 0, l => leafProduct encA encB (starsToNines l)
  | e + 1, l => sumAtLastStar (dpValueD encA encB e) l

/-- The value that is stored for the box l: what the dynamic program of Lemma 29 computes for it, at
its number of stars. -/
def storedD (encA encB : List ℤ) (l : List ℕ) : ℤ := dpValueD encA encB (starCount l) l

/-- On the arrays of two encodings, the product at the digits of a leaf is the product of its two
numbers. -/
theorem leafProduct_digitsT {L : ℕ} (encA encB : Leaf L → ℤ) (τ : Leaf L) :
    leafProduct (arrT encA) (arrT encB) (digitsT τ) = encA τ * encB τ := by
  rw [leafProduct, ofDigitList_digitsT, getD_arrT, getD_arrT]

/-- The dynamic program on digits, run on the arrays of the two encodings, is the dynamic program
of Lemma 29. -/
theorem dpValueD_digitsC {L : ℕ} (encA encB : Leaf L → ℤ) (e : ℕ) (π : Cube L) :
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
    · rw [dif_neg h, (lastStar_digitsC_eq_none_iff π).mpr (Finset.not_nonempty_iff_eq_empty.mp h)]



/-- The strings of n digits below 10 with between lo and hi digits 9, in lexicographic order. -/
def nineStrs : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, lo, _ => if lo = 0 then [[]] else []
  | n + 1, lo, hi =>
    (List.range 9).flatMap (fun d => (nineStrs n lo hi).map (d :: ·)) ++
      (if hi = 0 then [] else (nineStrs n (lo - 1) (hi - 1)).map (9 :: ·))

/-- The least string of n digits with at least lo digits 9: zeros, then lo nines. -/
def nineFirst (n lo : ℕ) : List ℕ := List.replicate (n - lo) 0 ++ List.replicate lo 9

/-- The first digit d raised by one, if that is possible, and the least admissible string of n
digits behind it. -/
def nineRaise (lo hi n d : ℕ) : Option (List ℕ) :=
  if d < 8 then some ((d + 1) :: nineFirst n lo)
  else if d = 8 ∧ 0 < hi then some (9 :: nineFirst n (lo - 1))
  else none

/-- The string after l, or none if l is the last one: the rest of the string goes to the string
after it, or, if it is the last one, the first digit is raised. -/
def nineNext : ℕ → ℕ → List ℕ → Option (List ℕ)
  | _, _, [] => none
  | lo, hi, d :: l =>
    match nineNext (if d = 9 then lo - 1 else lo) (if d = 9 then hi - 1 else hi) l with
    | some l' => some (d :: l')
    | none => nineRaise lo hi l.length d

/-- The string number i of the list, as a routine reaches it: from the first string by going to the
next one i times. -/
def nineStr (n lo hi i : ℕ) : List ℕ := (fun l => (nineNext lo hi l).getD l)^[i] (nineFirst n lo)

/-! ## The members of the list -/

/-- The first digit is below 9, or it is a 9 and counts. -/
theorem cons_mem_nineStrs {n lo hi d : ℕ} {l : List ℕ} :
    d :: l ∈ nineStrs (n + 1) lo hi ↔
      (d < 9 ∧ l ∈ nineStrs n lo hi) ∨ (d = 9 ∧ hi ≠ 0 ∧ l ∈ nineStrs n (lo - 1) (hi - 1)) := by
  rw [nineStrs, List.mem_append, List.mem_flatMap]
  refine or_congr ?_ ?_
  · simp only [List.mem_range, List.mem_map, List.cons.injEq]
    exact ⟨fun ⟨a, ha, l', hl', had, hll⟩ => ⟨had ▸ ha, hll ▸ hl'⟩,
      fun ⟨hd, hl⟩ => ⟨d, hd, l, hl, rfl, rfl⟩⟩
  · by_cases hhi : hi = 0
    · simp [hhi]
    · simp only [if_neg hhi, List.mem_map, List.cons.injEq]
      exact ⟨fun ⟨l', hl', hd, hll⟩ => ⟨hd.symm, hhi, hll ▸ hl'⟩,
        fun ⟨hd, _, hl⟩ => ⟨l, hl, hd.symm, rfl⟩⟩

theorem mem_nineStrs {n lo hi : ℕ} (l : List ℕ) :
    l ∈ nineStrs n lo hi ↔
      l.length = n ∧ (∀ d ∈ l, d < 10) ∧ lo ≤ l.count 9 ∧ l.count 9 ≤ hi := by
  induction n generalizing lo hi l with
  | zero => cases l <;> by_cases h : lo = 0 <;> simp [nineStrs, h]
  | succ n ih =>
    rcases l with _ | ⟨d, l⟩
    · simp [nineStrs]
    rw [cons_mem_nineStrs, ih, ih, List.length_cons, List.forall_mem_cons,
      Nat.add_right_cancel_iff]
    by_cases hd : d = 9
    · -- a nine less is needed, and a nine less is allowed, in the rest
      subst hd
      rw [List.count_cons_self]
      grind
    · rw [List.count_cons_of_ne hd]
      grind

theorem length_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    l.length = n :=
  ((mem_nineStrs l).1 hl).1

/-- The digit of the star does not occur. -/
theorem ten_notMem_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    10 ∉ l :=
  fun h => absurd (((mem_nineStrs l).1 hl).2.1 10 h) (lt_irrefl 10)

/-- There is no string with more nines than digits, or if the bounds contradict each other. -/
theorem nineStrs_eq_nil {n lo hi : ℕ} (h : n < lo ∨ hi < lo) : nineStrs n lo hi = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro l hl
  obtain ⟨hlen, -, hlo, hhi⟩ := (mem_nineStrs l).1 hl
  have := List.count_le_length (a := 9) (l := l)
  omega

/-- The list is strictly increasing in the lexicographic order. -/
theorem pairwise_lt_nineStrs (n lo hi : ℕ) : (nineStrs n lo hi).Pairwise (· < ·) := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs <;> simp
  | succ n ih =>
    rw [nineStrs, List.pairwise_append, List.pairwise_flatMap]
    refine ⟨⟨fun d _ => ?_, ?_⟩, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (ih lo hi).imp fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩)
    · refine List.pairwise_lt_range.imp fun {a b} hab x hx y hy => ?_
      obtain ⟨x', -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
      exact List.cons_lt_cons_iff.2 (Or.inl hab)
    · split_ifs
      · simp
      · rw [List.pairwise_map]
        exact (ih _ _).imp fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩)
    · intro x hx y hy
      obtain ⟨d, hd, hx⟩ := List.mem_flatMap.1 hx
      obtain ⟨x', -, rfl⟩ := List.mem_map.1 hx
      split_ifs at hy
      · simp at hy
      · obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
        exact List.cons_lt_cons_iff.2 (Or.inl (List.mem_range.1 hd))

theorem nineStrs_nodup (n lo hi : ℕ) : (nineStrs n lo hi).Nodup :=
  (pairwise_lt_nineStrs n lo hi).imp fun h => ne_of_lt h

/-! ## The length of the list -/

/-- The recursion for the length of the list. -/
theorem length_nineStrs_succ (n lo hi : ℕ) :
    (nineStrs (n + 1) lo hi).length = 9 * (nineStrs n lo hi).length
      + if hi = 0 then 0 else (nineStrs n (lo - 1) (hi - 1)).length := by
  rw [nineStrs, List.length_append, List.length_flatMap]
  congr 1
  · simp only [List.length_map, List.map_const', List.length_range, List.sum_replicate_nat]
  · split_ifs <;> simp

/-- Strings without a nine: one more digit, nine times as many. -/
theorem nineTerm_zero (n : ℕ) :
    (n + 1).choose 0 * 9 ^ (n + 1 - 0) = 9 * (n.choose 0 * 9 ^ (n - 0)) := by
  simp [pow_succ, mul_comm]

/-- Strings with g + 1 nines: the first digit is a nine or one of the nine other digits. -/
theorem nineTerm_succ (n g : ℕ) :
    (n + 1).choose (g + 1) * 9 ^ (n + 1 - (g + 1))
      = n.choose g * 9 ^ (n - g) + 9 * (n.choose (g + 1) * 9 ^ (n - (g + 1))) := by
  rw [Nat.choose_succ_succ, Nat.add_sub_add_right, add_mul]
  congr 1
  rcases Nat.lt_or_ge n (g + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    simp
  · rw [show n - g = n - (g + 1) + 1 by omega, pow_succ]
    ring

/-- A sum from 0: the first summand apart. -/
theorem sum_Icc_zero_succ (h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc 0 (h + 1), G f = G 0 + ∑ g ∈ Finset.Icc 0 h, G (g + 1) := by
  rw [← Nat.range_succ_eq_Icc_zero, ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ', add_comm]

/-- A sum with both ends shifted by one. -/
theorem sum_Icc_succ_succ (l h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc (l + 1) (h + 1), G f = ∑ g ∈ Finset.Icc l h, G (g + 1) := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-- There are binom(n, f) 9^{n-f} strings with exactly f nines. -/
theorem length_nineStrs (n lo hi : ℕ) :
    (nineStrs n lo hi).length = ∑ f ∈ Finset.Icc lo hi, n.choose f * 9 ^ (n - f) := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs with h
    · subst h
      rw [Finset.sum_eq_single_of_mem 0 (by simp) fun b _ hb => by
        rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb), zero_mul]]
      rfl
    · refine (Finset.sum_eq_zero fun f hf => ?_).symm
      have := (Finset.mem_Icc.1 hf).1
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  | succ n ih =>
    rw [length_nineStrs_succ, ih]
    rcases hi with _ | h
    · -- no nine is allowed
      rw [if_pos rfl, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      obtain rfl : f = 0 := Nat.le_zero.mp (Finset.mem_Icc.1 hf).2
      exact (nineTerm_zero n).symm
    · rw [if_neg (Nat.succ_ne_zero h), ih, Nat.add_sub_cancel]
      rcases lo with _ | l
      · rw [sum_Icc_zero_succ, sum_Icc_zero_succ, nineTerm_zero, Nat.zero_sub, mul_add,
          Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
        refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
        rw [nineTerm_succ, add_comm]
      · rw [sum_Icc_succ_succ, sum_Icc_succ_succ, Nat.add_sub_cancel, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [nineTerm_succ, add_comm]

/-! ## The first string -/

/-- If there is a string at all, the bounds are consistent. -/
theorem le_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    lo ≤ n ∧ lo ≤ hi := by
  obtain ⟨hlen, -, hlo, hhi⟩ := (mem_nineStrs l).1 hl
  have := List.count_le_length (a := 9) (l := l)
  omega

/-- The least string begins with 0 if not all digits have to be nines. -/
theorem nineFirst_succ {n lo : ℕ} (h : lo ≤ n) :
    nineFirst (n + 1) lo = 0 :: nineFirst n lo := by
  rw [nineFirst, nineFirst, Nat.succ_sub h, List.replicate_succ, List.cons_append]

/-- The string of nines. -/
theorem nineFirst_self_succ (n : ℕ) : nineFirst (n + 1) (n + 1) = 9 :: nineFirst n n := by
  simp [nineFirst, List.replicate_succ]

/-- Without strings of n digits there are no strings of n + 1 digits that begin below 9. -/
theorem flatMap_map_nil (l : List ℕ) :
    l.flatMap (fun d => ([] : List (List ℕ)).map (d :: ·)) = [] :=
  List.flatMap_eq_nil_iff.2 fun _ _ => rfl

theorem head?_nineStrs {n lo hi : ℕ} (h : lo ≤ n) (h' : lo ≤ hi) :
    (nineStrs n lo hi).head? = some (nineFirst n lo) := by
  induction n generalizing lo hi with
  | zero =>
    obtain rfl : lo = 0 := by omega
    rfl
  | succ n ih =>
    rw [nineStrs]
    rcases Nat.lt_or_ge n lo with hlo | hlo
    · -- all digits are nines
      obtain rfl : lo = n + 1 := by omega
      rw [nineStrs_eq_nil (Or.inl (Nat.lt_succ_self n)), if_neg (by omega), flatMap_map_nil,
        List.nil_append, List.head?_map, Nat.add_sub_cancel, ih le_rfl (by omega),
        nineFirst_self_succ]
      rfl
    · rw [List.range_succ_eq_map, List.flatMap_cons, List.append_assoc, List.head?_append,
        List.head?_map, ih hlo h', nineFirst_succ hlo]
      rfl

/-! ## From each string to the next -/

/-- f takes each member of the list to the following one, and the last one to z. -/
def NextTo {α : Type} (f : α → Option α) : List α → Option α → Prop
  | [], _ => True
  | x :: r, z => f x = r.head?.or z ∧ NextTo f r z

/-- f goes through two lists one after the other exactly if it goes through both, and from the last
member of the first list to the first member of the second (to z if the second list is empty). -/
theorem nextTo_append {α : Type} {f : α → Option α} {A B : List α} {z : Option α} :
    NextTo f (A ++ B) z ↔ NextTo f A (B.head?.or z) ∧ NextTo f B z := by
  induction A with
  | nil => simp [NextTo]
  | cons x A ih =>
    rw [List.cons_append, NextTo, NextTo, ih, List.head?_append, Option.or_assoc, and_assoc]

/-- What `NextTo` says about the member number i. -/
theorem NextTo.getElem {α : Type} {f : α → Option α} {A : List α} {z : Option α}
    (h : NextTo f A z) (i : ℕ) (hi : i < A.length) : f A[i] = A[i + 1]?.or z := by
  induction A generalizing i with
  | nil => simp at hi
  | cons x A ih =>
    cases i with
    | zero => rw [List.getElem_cons_zero, h.1, List.getElem?_cons_succ, List.head?_eq_getElem?]
    | succ i =>
      rw [List.getElem_cons_succ, List.getElem?_cons_succ]
      exact ih h.2 i (by simpa using hi)

/-- The block of the strings with the first digit d. -/
theorem nextTo_map_cons (lo hi n d : ℕ) (S : List (List ℕ)) (hS : ∀ l ∈ S, l.length = n)
    (h : NextTo (nineNext (if d = 9 then lo - 1 else lo) (if d = 9 then hi - 1 else hi)) S none) :
    NextTo (nineNext lo hi) (S.map (d :: ·)) (nineRaise lo hi n d) := by
  induction S with
  | nil => trivial
  | cons x r ih =>
    refine ⟨?_, ih (fun l hl => hS l (by simp [hl])) h.2⟩
    rw [nineNext, h.1, Option.or_none]
    rcases r with _ | ⟨y, r⟩
    · simp only [List.head?_nil, List.map_nil, Option.none_or, hS x (by simp)]
    · rfl

/-- The blocks of the strings with the first digits a, a + 1, …, a + k - 1, followed by the block
with the first digit 9: the end of the list `nineStrs (n + 1) lo hi`. -/
def nineBlocks (n lo hi a k : ℕ) : List (List ℕ) :=
  (List.range' a k).flatMap (fun d => (nineStrs n lo hi).map (d :: ·)) ++
    (if hi = 0 then [] else (nineStrs n (lo - 1) (hi - 1)).map (9 :: ·))

section

variable {n lo hi : ℕ}

/-- `nineNext` goes through the last block, the strings with the first digit 9. -/
theorem nextTo_nineBlocks_zero (a : ℕ)
    (h9 : NextTo (nineNext (lo - 1) (hi - 1)) (nineStrs n (lo - 1) (hi - 1)) none) :
    NextTo (nineNext lo hi) (nineBlocks n lo hi a 0) none := by
  rw [nineBlocks, List.range'_zero, List.flatMap_nil, List.nil_append]
  split_ifs
  · trivial
  · exact nextTo_map_cons lo hi n 9 _ (fun _ => length_of_mem_nineStrs) h9

/-- The first string after the block with the first digit a is the one to which `nineNext` goes by
raising the digit a. -/
theorem head_nineBlocks (hn : lo ≤ n) (hh : lo ≤ hi) {a k : ℕ} (hak : a + 1 + k = 9) :
    (nineBlocks n lo hi (a + 1) k).head? = nineRaise lo hi n a := by
  rw [nineBlocks, nineRaise]
  cases k with
  | zero =>
    obtain rfl : a = 8 := by omega
    rw [List.range'_zero, List.flatMap_nil, List.nil_append]
    by_cases h0 : hi = 0
    · simp [h0]
    · rw [if_neg h0, List.head?_map, head?_nineStrs (by omega) (by omega), if_neg (lt_irrefl 8),
        if_pos ⟨rfl, Nat.pos_of_ne_zero h0⟩]
      rfl
  | succ k =>
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc, List.head?_append, List.head?_map,
      head?_nineStrs hn hh, if_pos (show a < 8 by omega)]
    rfl

/-- `nineNext` goes through the blocks. -/
theorem nextTo_nineBlocks (hn : lo ≤ n) (hh : lo ≤ hi)
    (h : NextTo (nineNext lo hi) (nineStrs n lo hi) none)
    (h9 : NextTo (nineNext (lo - 1) (hi - 1)) (nineStrs n (lo - 1) (hi - 1)) none) (k a : ℕ)
    (hak : a + k = 9) : NextTo (nineNext lo hi) (nineBlocks n lo hi a k) none := by
  induction k generalizing a with
  | zero => exact nextTo_nineBlocks_zero a h9
  | succ k ih =>
    have hsplit : nineBlocks n lo hi a (k + 1)
        = (nineStrs n lo hi).map (a :: ·) ++ nineBlocks n lo hi (a + 1) k := by
      rw [nineBlocks, nineBlocks, List.range'_succ, List.flatMap_cons, List.append_assoc]
    rw [hsplit, nextTo_append, Option.or_none, head_nineBlocks hn hh (by omega)]
    refine ⟨nextTo_map_cons lo hi n a _ (fun _ => length_of_mem_nineStrs) ?_, ih (a + 1) (by omega)⟩
    rwa [if_neg (by omega), if_neg (by omega)]

end

/-- `nineNext` goes through the list. -/
theorem nextTo_nineStrs (n lo hi : ℕ) :
    NextTo (nineNext lo hi) (nineStrs n lo hi) none := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs
    · exact ⟨rfl, trivial⟩
    · trivial
  | succ n ih =>
    by_cases h : lo ≤ n ∧ lo ≤ hi
    · rw [nineStrs, List.range_eq_range']
      exact nextTo_nineBlocks h.1 h.2 (ih lo hi) (ih _ _) 9 0 rfl
    · -- only strings that begin with a nine
      rw [nineStrs, nineStrs_eq_nil (by omega), flatMap_map_nil]
      exact nextTo_nineBlocks_zero 0 (ih _ _)

/-- `nineNext` goes from each string of the list to the following one, and from the last one to
none. -/
theorem nineNext_getElem (n lo hi i : ℕ) (h : i < (nineStrs n lo hi).length) :
    nineNext lo hi ((nineStrs n lo hi)[i]) = (nineStrs n lo hi)[i + 1]? := by
  rw [(nextTo_nineStrs n lo hi).getElem i h, Option.or_none]

section

variable {n lo hi i : ℕ}

theorem nineStr_succ (n lo hi i : ℕ) :
    nineStr n lo hi (i + 1) = (nineNext lo hi (nineStr n lo hi i)).getD (nineStr n lo hi i) :=
  Function.iterate_succ_apply' _ _ _

/-- `nineStr n lo hi i` is the member number i of the list. -/
theorem getElem_nineStrs (h : i < (nineStrs n lo hi).length) :
    (nineStrs n lo hi)[i] = nineStr n lo hi i := by
  induction i with
  | zero =>
    obtain ⟨hn, hh⟩ := le_of_mem_nineStrs (List.getElem_mem h)
    refine Option.some.inj ?_
    rw [← List.getElem?_eq_getElem h, ← List.head?_eq_getElem?, head?_nineStrs hn hh]
    rfl
  | succ i ih =>
    rw [nineStr_succ, ← ih (Nat.lt_of_succ_lt h), nineNext_getElem, List.getElem?_eq_getElem h]
    rfl

theorem nineStr_mem (h : i < (nineStrs n lo hi).length) : nineStr n lo hi i ∈ nineStrs n lo hi :=
  getElem_nineStrs h ▸ List.getElem_mem h

/-- There is a next string exactly if the string is not the last one of the list. -/
theorem isSome_nineNext_nineStr (h : i < (nineStrs n lo hi).length) :
    (nineNext lo hi (nineStr n lo hi i)).isSome = decide (i + 1 < (nineStrs n lo hi).length) := by
  rw [← getElem_nineStrs h, nineNext_getElem]
  by_cases h' : i + 1 < (nineStrs n lo hi).length <;> simp [h']

/-- If the bounds are consistent, there is a string. -/
theorem length_nineStrs_pos (hn : lo ≤ n) (hh : lo ≤ hi) : 0 < (nineStrs n lo hi).length :=
  List.length_pos_iff.mpr fun hnil => by simpa [hnil] using head?_nineStrs hn hh

end

end ThreeSumApsp.Spec

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The boxes of an output string, from its leaves of order exactly `t` (Section 4.2)

Let `η` be an output string (the paper's w) with inner set `Q` of `m` levels. The boxes of `η` are
the cubes of the sets `𝓑_V`, over all `V ⊆ Q` with `|V| = m - t`. This file proves two passages of
the running text of Section 4.2 about them.

* *Every box of `η` has exactly `m - t` symbols that are `P₀` or stars*
  (`card_starLevels_add_card_P0Levels`).
* *The second description.* Take a leaf of order exactly `t` contributing to `η` and replace its
  `P₀` by a star at every level of `Q` below the lowest level of `Q` at which it chooses another
  term, or at every level of `Q` if `t = 0` (`starBelow`). For such a leaf this is the box of the
  leaf (`boxOfLeaf_eq_starBelow`), so it is a box of `η` (`starBelow_mem`). Replacing the stars with
  `P₀` gives the leaf back (`starsToP0_starBelow`), and it turns every box of `η` into a leaf of
  order exactly `t` contributing to `η` (`starsToP0_of_mem`). So each box of `η` arises exactly once
  (`existsUnique_starBelow_eq`).
-/


open Finset

namespace ThreeSumApsp

variable {L m t : ℕ} {η : OutStr L} {τ : Leaf L}

/-- Section 4.2, for a leaf `τ` of order exactly `t` contributing to `η`: "consider the lowest level
of Q at which it chooses a term other than P₀, and replace its P₀ by a star at every lower level of
Q (or at every level of Q, if t = 0)." With `Z` the set of the levels of `Q` at which `τ` chooses
`P₀`, these lower levels are those of `F_Z`, which is all of `Q` if `Z = Q`. -/
def starBelow (η : OutStr L) (τ : Leaf L) : Cube L :=
  Cube.starAt (FV (innerSetO η) (Zof (innerSetO η) τ)) τ

/-- A leaf of order exactly `t` contributing to `η` chooses `P₀` at exactly `m - t` levels. -/
lemma card_Zof_eq (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    (Zof (innerSetO η) τ).card = m - t := by
  have := order_eq_sub_card_Zof m η τ hτ
  omega

/-- A set `Z` of `m - t` levels needs no padding: `V = Z`. -/
lemma Vof_eq_self (Q Z : Finset (Fin L)) (hZ : Z.card = m - t) : Vof m t Q Z = Z := by
  simp [Vof, lowest, hZ]

/-- For a leaf of order exactly `t` contributing to `η`, the cube of the second description is the
box of the leaf. -/
theorem boxOfLeaf_eq_starBelow (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    boxOfLeaf m t η τ = starBelow η τ := by
  rw [boxOfLeaf, starBelow, Vof_eq_self _ _ (card_Zof_eq hτ hord)]

/-- Section 4.2: "The result is a box of w". -/
theorem starBelow_mem (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    starBelow η τ ∈ (Vsets m t η).biUnion (BV η) := by
  have hmem := boxOfLeaf_mem_BV m t hτ
  rw [boxOfLeaf_eq_starBelow hτ hord, Vof_eq_self _ _ (card_Zof_eq hτ hord)] at hmem
  exact mem_biUnion.2 ⟨_, mem_powersetCard.2 ⟨filter_subset _ _, card_Zof_eq hτ hord⟩, hmem⟩

end ThreeSumApsp


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# What a query reads (proof of Theorem 30, "Query")

The output string, which the paper calls w, is η as a string of variables and w as the list of its
digits; the levels of its inner set Q are the positions of the digit 9.  w is also the list of
digits of the private leaf of η, and `scatter w s` replaces its m nines by a string s of m digits:
the paper's "forming its leaf or its box from the private leaf".  A query adds up the products at
the leaves of order below t contributing to η, and the stored values of the boxes of η (steps (2)
and (3) of the query in Section 4.3).

* `lowList`: the strings with at least m - t + 1 nines give the leaves of order below t ("Each of
  these leaves is obtained from the private leaf of w, which has P₀ at every level of Q, by picking
  fewer than t of those levels and replacing P₀ with one of the nine other terms at each of them");
* `boxesOf`: the strings with exactly m - t nines give the leaves of order exactly t, and `starRun`
  turns the leading nines into stars.  This is the second description of the boxes of w in
  Section 4.2: "For such a leaf, consider the lowest level of Q at which it chooses a term other
  than P₀, and replace its P₀ by a star at every lower level of Q (or at every level of Q, if
  t = 0).  The result is a box of w, and each box of w arises exactly once in this way".  On cubes
  the result is `starBelow`, and the members of the list are exactly the strings of the cubes
  `starBelow η τ` for these leaves τ (`mem_boxesOf_iff`; no other proof rests on this statement).
  In the first description the nines are the levels of V, and the leading nines those of F_V, which
  "is the longest initial segment of Q contained in V".  `starRunIf` is `starRun` as a pass over the
  string with one flag.

The results are `sum_lowList` and `sum_boxesOf` (a sum over one of the lists is the sum over the set
of the paper) and `sum_queryTerms_storedD` (the numbers that a query adds up have the sum of the
query of the paper). Each list is compared with its set by counting
(`List.sum_map_eq_sum_of_length_eq_card`):
1. The list has no repetitions: `scatter w` is injective on strings of m digits, and `starRun` can
   be undone (`lowList_nodup`, `boxesOf_nodup`).
2. Each member is the list of digits of a member of the set.  `scatter w s` is a leaf τ contributing
   to η with as many symbols P₀ as s has nines (`exists_leaf_scatter`).  With at least m - t + 1
   nines its order is below t (`exists_of_mem_lowList`).  With exactly m - t nines its order is t.
   The cube `starBelow η τ` has the digits of τ with stars at the levels of F_Z, where Z, the set
   of the levels of Q at which τ chooses P₀, is the nines of s.  `Unreached` is the formula for F_Z
   read on digits (`unreached_iff_mem_FV`); it holds exactly at the leading nines of s
   (`getD_scatter_starRun`), so the cube has the digits `scatter w (starRun s)`
   (`digitsC_starBelow`, `exists_leaf_of_mem_boxesOf`), and it is a box of η (`starBelow_mem`,
   `exists_of_mem_boxesOf`).
3. The lists have ∑_{d<t} α_d and α_t members (`length_lowList`, `length_boxesOf`), and so have the
   sets, by the last line of Lemma 28 (`lemma_28_counts`).
-/


namespace ThreeSumApsp.Spec

/-- The list w with its digits 9 replaced, from the left, by the digits of s. -/
def scatter : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x :: w, [] => x :: w
  | x :: w, d :: s => if x = 9 then d :: scatter w s else x :: scatter w (d :: s)

/-- The leaves of order below t contributing to the output string with the digits w, in
lexicographic order: at the m levels of Q they have at least m - t + 1 digits 9. -/
def lowList (m t : ℕ) (w : List ℕ) : List (List ℕ) := (nineStrs m (m - t + 1) m).map (scatter w)

/-- The leading digits 9 turned into 10: F_V "is the longest initial segment of Q contained in V"
(Section 4.2). -/
def starRun : List ℕ → List ℕ
  | [] => []
  | d :: l => if d = 9 then 10 :: starRun l else d :: l

/-- The boxes of the output string with the digits w.  "There is another way to describe the boxes
of w, in terms of the leaves of order exactly t contributing to w.  For such a leaf, consider the
lowest level of Q at which it chooses a term other than P₀, and replace its P₀ by a star at every
lower level of Q (or at every level of Q, if t = 0)" (Section 4.2).  Such a leaf has at the m levels
of Q a string with exactly m - t digits 9, and the leading ones are turned into stars
(`mem_boxesOf_iff`). -/
def boxesOf (m t : ℕ) (w : List ℕ) : List (List ℕ) :=
  (nineStrs m (m - t) (m - t)).map fun s => scatter w (starRun s)

/-- The numbers that a query adds up, in the order in which it adds them: the products at the leaves
of `lowList`, read from the two encodings, then the stored values of the boxes of `boxesOf`;
`stored l` is the value stored for the box l. -/
def queryTerms (m t : ℕ) (encA encB : List ℤ) (stored : List ℕ → ℤ) (w : List ℕ) : List ℤ :=
  (lowList m t w).map (leafProduct encA encB) ++ (boxesOf m t w).map stored

/-! ## Putting a string at the positions of the nines -/

theorem scatter_nil_right (w : List ℕ) : scatter w [] = w := by
  cases w <;> rfl

/-- A digit other than 9 is kept. -/
theorem scatter_cons_of_ne {x : ℕ} (hx : x ≠ 9) (w s : List ℕ) :
    scatter (x :: w) s = x :: scatter w s := by
  cases s with
  | nil => rw [scatter_nil_right, scatter_nil_right]
  | cons d s => simp [scatter, hx]

/-- A digit 9 is replaced by the next digit of the string. -/
theorem scatter_nine_cons (w : List ℕ) (d : ℕ) (s : List ℕ) :
    scatter (9 :: w) (d :: s) = d :: scatter w s := by
  simp [scatter]

/-- The string has the length of w. -/
theorem length_scatter (w s : List ℕ) : (scatter w s).length = w.length := by
  fun_induction scatter w s <;> simp_all

/-- Every digit of `scatter w s` is a digit of w or of s. -/
theorem mem_of_mem_scatter {w s : List ℕ} {d : ℕ} (h : d ∈ scatter w s) :
    d ∈ w ∨ d ∈ s := by
  fun_induction scatter w s <;> grind

/-- At a position where w has no 9, its digit is kept. -/
theorem getD_scatter_of_ne (w s : List ℕ) (i : ℕ) (h : w.getD i 0 ≠ 9) :
    (scatter w s).getD i 0 = w.getD i 0 := by
  fun_induction scatter w s generalizing i <;> cases i <;> simp_all

/-- `scatter w s` has as many nines as s. -/
theorem count_nine_scatter (w s : List ℕ) (hs : s.length = w.count 9) :
    (scatter w s).count 9 = s.count 9 := by
  fun_induction scatter w s <;> grind

/-- Strings of the right length are determined by what `scatter w` makes of them. -/
theorem scatter_inj (w s s' : List ℕ) (hs : s.length = w.count 9)
    (hs' : s'.length = w.count 9) (h : scatter w s = scatter w s') : s = s' := by
  fun_induction scatter w s generalizing s' <;> cases s' <;> grind [scatter]

/-! ## The leading nines turned into stars -/

theorem length_starRun (s : List ℕ) : (starRun s).length = s.length := by
  fun_induction starRun s <;> simp_all

/-- Turning the stars back into nines undoes `starRun`. -/
theorem starsToNines_starRun {s : List ℕ} (h : 10 ∉ s) : starsToNines (starRun s) = s := by
  fun_induction starRun s with
  | case1 => rfl
  | case2 l ih => simp_all [starsToNines]
  | case3 d l hd => exact starsToNines_of_notMem h

/-- `starRun` continued on the rest of a string that is read digit by digit: flag says that all the
digits read so far were nines, so the run of stars goes on; otherwise the rest is kept. -/
def starRunIf (flag : Bool) (s : List ℕ) : List ℕ := if flag then starRun s else s

/-- A digit other than 9 ends the run. -/
theorem starRunIf_cons_of_ne {d : ℕ} (hd : d ≠ 9) (flag : Bool) (s : List ℕ) :
    starRunIf flag (d :: s) = d :: starRunIf false s := by
  cases flag <;> simp [starRunIf, starRun, hd]

/-- A digit 9 becomes a star while the run goes on, and the run goes on. -/
theorem starRunIf_nine_cons (flag : Bool) (s : List ℕ) :
    starRunIf flag (9 :: s) = (if flag then 10 else 9) :: starRunIf flag s := by
  cases flag <;> simp [starRunIf, starRun]

/-- Position i is one of "the levels that we have not reached" (F_V, Section 4.2).  Here w is the
list of digits of the output string, so its nines are the levels of Q, and u is the list of digits
of a leaf, whose nines among them are the levels of V: i is a level of Q below every level of Q ∖ V.
-/
def Unreached (w u : List ℕ) (i : ℕ) : Prop :=
  w.getD i 0 = 9 ∧ ∀ j, w.getD j 0 = 9 → u.getD j 0 ≠ 9 → i < j

/-- The first position is not reached if it is a level of V. -/
theorem unreached_cons_zero (x y : ℕ) (w u : List ℕ) :
    Unreached (x :: w) (y :: u) 0 ↔ x = 9 ∧ y = 9 := by
  rw [Unreached, ← Nat.and_forall_add_one]
  simp only [List.getD_cons_zero, lt_irrefl, Nat.zero_lt_succ, implies_true, and_true]
  tauto

/-- A later position is not reached if the first position is no level of Q ∖ V and the position is
not reached in the rest. -/
theorem unreached_cons_succ (x y : ℕ) (w u : List ℕ) (i : ℕ) :
    Unreached (x :: w) (y :: u) (i + 1) ↔ (x = 9 → y = 9) ∧ Unreached w u i := by
  rw [Unreached, Unreached, ← Nat.and_forall_add_one]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.not_lt_zero, Nat.add_lt_add_iff_right]
  tauto

/-- Turning the leading nines of s into stars puts stars at the positions given by the formula for
F_V, and changes nothing else. -/
theorem getD_scatter_starRun (w s : List ℕ) (hs : s.length = w.count 9) (i : ℕ) :
    (Unreached w (scatter w s) i → (scatter w (starRun s)).getD i 0 = 10) ∧
      (¬ Unreached w (scatter w s) i →
        (scatter w (starRun s)).getD i 0 = (scatter w s).getD i 0) := by
  induction w generalizing s i with
  | nil => simp [scatter, Unreached]
  | cons x w ih =>
    by_cases hx : x = 9
    · subst hx
      rw [List.count_cons_self] at hs
      obtain ⟨d, s, rfl⟩ := List.exists_cons_of_length_eq_add_one hs
      by_cases hd : d = 9
      · subst hd
        rw [starRun, if_pos rfl, scatter_nine_cons, scatter_nine_cons]
        cases i with
        | zero => simp [unreached_cons_zero]
        | succ i => simpa [unreached_cons_succ] using ih s (by simpa using hs) i
      · rw [starRun, if_neg hd, scatter_nine_cons]
        exact ⟨fun h => absurd (h.2 0 rfl hd) (Nat.not_lt_zero i), fun _ => rfl⟩
    · rw [List.count_cons_of_ne hx] at hs
      rw [scatter_cons_of_ne hx, scatter_cons_of_ne hx]
      cases i with
      | zero => simp [unreached_cons_zero, hx]
      | succ i => simpa [unreached_cons_succ, hx] using ih s hs i

/-! ## The leaves of order below t -/


variable {L m t : ℕ} {η : OutStr L}

/-- The output string has m nines. -/
theorem count_nine_digitsO (hη : (innerSetO η).card = m) :
    (digitsO η).count 9 = m := by
  rw [← card_innerSetO, hη]

/-- A string of digits below 10, put at the levels of Q, gives a leaf contributing to η that
chooses P₀ as often as the string has a nine. -/
theorem exists_leaf_scatter {s : List ℕ} (hlen : s.length = (digitsO η).count 9)
    (hdig : ∀ d ∈ s, d < 10) :
    ∃ τ : Leaf L, digitsT τ = scatter (digitsO η) s ∧ Leaf.Contributes τ η ∧
      (P0Levels τ).card = s.count 9 := by
  obtain ⟨τ, hτ⟩ := exists_digitsT (L := L) (scatter (digitsO η) s)
    (by rw [length_scatter, length_digitsO])
    fun d hd => (mem_of_mem_scatter hd).elim (digitsO_lt η d) (hdig d)
  refine ⟨τ, hτ, fun ℓ => ?_, ?_⟩
  · rw [contributes_iff, ← getD_digitsO, ← getD_digitsT, hτ]
    by_cases h9 : (digitsO η).getD ℓ 0 = 9
    · exact Or.inl h9
    · exact Or.inr (getD_scatter_of_ne _ _ _ h9)
  · rw [card_P0Levels, hτ, count_nine_scatter _ _ hlen]

/-- Every member of the list is the list of digits of a leaf of order below t contributing to η. -/
theorem exists_of_mem_lowList (hη : (innerSetO η).card = m) (l : List ℕ)
    (h : l ∈ lowList m t (digitsO η)) : ∃ τ ∈ lowLeaves m t η, digitsT τ = l := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  obtain ⟨hlen, hdig, hlo, -⟩ := (mem_nineStrs s).mp hs
  obtain ⟨τ, hτ, hcontr, hcard⟩ :=
    exists_leaf_scatter (hlen.trans (count_nine_digitsO hη).symm) hdig
  refine ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontr, ?_⟩, hτ⟩
  -- the order is m minus the number of nines, of which there are at least m - t + 1 (hlo)
  rw [order, hcard]
  omega

theorem lowList_nodup (hη : (innerSetO η).card = m) : (lowList m t (digitsO η)).Nodup := by
  have hcount := count_nine_digitsO hη
  exact (nineStrs_nodup _ _ _).map_on fun s hs s' hs' h => scatter_inj _ s s'
    (by rw [length_of_mem_nineStrs hs, hcount]) (by rw [length_of_mem_nineStrs hs', hcount]) h

/-- There are ∑_{d < t} α_d such leaves. -/
theorem length_lowList (ht : t ≤ m) (w : List ℕ) :
    (lowList m t w).length = ∑ d ∈ Finset.range t, alpha m d := by
  rw [lowList, List.length_map, length_nineStrs]
  -- a string with f nines gives a leaf of order d = m - f: reflect the sum
  refine Finset.sum_nbij' (fun f => m - f) (fun d => m - d) ?_ ?_ ?_ ?_
    fun f hf => by rw [alpha, Nat.choose_symm (Finset.mem_Icc.mp hf).2]
  all_goals
    simp only [Finset.mem_Icc, Finset.mem_range]
    intro a ha
    omega

/-- **The first sum of a query**: a sum over the list is the sum over the leaves of order below t
contributing to η. -/
theorem sum_lowList (ht : t ≤ m) (hη : (innerSetO η).card = m) (F : List ℕ → ℤ) :
    ((lowList m t (digitsO η)).map F).sum = ∑ τ ∈ lowLeaves m t η, F (digitsT τ) :=
  List.sum_map_eq_sum_of_length_eq_card _ (lowList_nodup hη) _ digitsT (digitsT_injective L)
    (exists_of_mem_lowList hη)
    ((length_lowList ht _).trans (lemma_28_counts m t ht η hη).1.symm) F

/-! ## The boxes -/

/-- The formula for F_V on digits is the formula of the paper, for V = Z. -/
theorem unreached_iff_mem_FV (τ : Leaf L) (ℓ : Fin L) :
    Unreached (digitsO η) (digitsT τ) ℓ ↔ ℓ ∈ FV (innerSetO η) (Zof (innerSetO η) τ) := by
  rw [Unreached, getD_digitsO_eq_nine, FV, Finset.mem_filter,
    forall_nine_digitsO η fun j => (digitsT τ).getD j 0 ≠ 9 → (ℓ : ℕ) < j]
  refine and_congr_right fun _ => ⟨fun h ℓ' hℓ' => ?_, fun h ℓ' hℓ' h9 => ?_⟩
  · obtain ⟨hQ, hZ⟩ := Finset.mem_sdiff.mp hℓ'
    refine h ℓ' hQ fun h9 => hZ (Finset.mem_filter.mpr ⟨hQ, ?_⟩)
    rwa [getD_digitsT, termIdx_eq_nine] at h9
  · refine h ℓ' (Finset.mem_sdiff.mpr ⟨hℓ', fun hZ => h9 ?_⟩)
    rw [getD_digitsT, termIdx_eq_nine]
    exact (Finset.mem_filter.mp hZ).2

/-- The cube of the second description of the boxes (Section 4.2): its digits are those of the leaf,
with the leading nines of the string at the levels of Q turned into stars. -/
theorem digitsC_starBelow {τ : Leaf L} {s : List ℕ} (hs : s.length = (digitsO η).count 9)
    (hτ : digitsT τ = scatter (digitsO η) s) :
    digitsC (starBelow η τ) = scatter (digitsO η) (starRun s) := by
  refine digitsC_eq_of_getD _ (by rw [length_scatter, length_digitsO]) fun ℓ => ?_
  obtain ⟨hstar, hterm⟩ := getD_scatter_starRun (digitsO η) s hs ℓ
  rw [← hτ, unreached_iff_mem_FV] at hstar hterm
  rw [starBelow, Cube.starAt]
  split_ifs with h
  · exact hstar h
  · rw [hterm h, getD_digitsT, cubeIdx_term]

/-- Every member of the list arises, as in the second description of the boxes, from a leaf of order
exactly t contributing to η. -/
theorem exists_leaf_of_mem_boxesOf (ht : t ≤ m) (hη : (innerSetO η).card = m) (l : List ℕ)
    (h : l ∈ boxesOf m t (digitsO η)) :
    ∃ τ : Leaf L, (Leaf.Contributes τ η ∧ order m τ = t) ∧ digitsC (starBelow η τ) = l := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  obtain ⟨hlen, hdig, hlo, hhi⟩ := (mem_nineStrs s).mp hs
  have : s.length = (digitsO η).count 9 := hlen.trans (count_nine_digitsO hη).symm
  obtain ⟨τ, hτ, hcontr, hcard⟩ := exists_leaf_scatter this hdig
  refine ⟨τ, ⟨hcontr, ?_⟩, digitsC_starBelow this hτ⟩
  -- exactly m - t nines (hlo, hhi): the order is t
  rw [order, hcard]
  omega

/-- Every member of the list is the list of digits of a box of η: "The result is a box of w". -/
theorem exists_of_mem_boxesOf (ht : t ≤ m) (hη : (innerSetO η).card = m) (l : List ℕ)
    (h : l ∈ boxesOf m t (digitsO η)) : ∃ π ∈ (Vsets m t η).biUnion (BV η), digitsC π = l := by
  obtain ⟨τ, ⟨hcontr, hord⟩, hl⟩ := exists_leaf_of_mem_boxesOf ht hη l h
  exact ⟨starBelow η τ, starBelow_mem hcontr hord, hl⟩

theorem boxesOf_nodup (hη : (innerSetO η).card = m) : (boxesOf m t (digitsO η)).Nodup := by
  have hcount := count_nine_digitsO hη
  refine (nineStrs_nodup _ _ _).map_on fun s hs s' hs' h => ?_
  have hrun := scatter_inj _ (starRun s) (starRun s')
    (by rw [length_starRun, length_of_mem_nineStrs hs, hcount])
    (by rw [length_starRun, length_of_mem_nineStrs hs', hcount]) h
  rw [← starsToNines_starRun (ten_notMem_of_mem_nineStrs hs), hrun,
    starsToNines_starRun (ten_notMem_of_mem_nineStrs hs')]

/-- "This means that w has exactly α_t boxes." -/
theorem length_boxesOf (ht : t ≤ m) (w : List ℕ) : (boxesOf m t w).length = alpha m t := by
  rw [boxesOf, List.length_map, length_nineStrs, Finset.Icc_self, Finset.sum_singleton, alpha,
    Nat.choose_symm ht, Nat.sub_sub_self ht]

/-- **The second sum of a query**: a sum over the list is the sum over the boxes of η. -/
theorem sum_boxesOf (ht : t ≤ m) (hη : (innerSetO η).card = m) (F : List ℕ → ℤ) :
    ((boxesOf m t (digitsO η)).map F).sum = ∑ π ∈ (Vsets m t η).biUnion (BV η), F (digitsC π) :=
  List.sum_map_eq_sum_of_length_eq_card _ (boxesOf_nodup hη) _ digitsC (digitsC_injective L)
    (exists_of_mem_boxesOf ht hη)
    ((length_boxesOf ht _).trans (lemma_28_counts m t ht η hη).2.2.symm) F


/-! ## The query -/

/-- With the values of the dynamic program for the boxes, the numbers that a query adds up have the
sum of the query of the proof of Theorem 30. -/
theorem sum_queryTerms_storedD {L m t : ℕ} (ht : t ≤ m) (encA encB : Leaf L → ℤ) {η : OutStr L}
    (hη : (innerSetO η).card = m) :
    (queryTerms m t (arrT encA) (arrT encB) (storedD (arrT encA) (arrT encB)) (digitsO η)).sum
      = queryValue m t encA encB η := by
  rw [queryTerms, List.sum_append, queryValue, sum_lowList ht hη, sum_boxesOf ht hη,
    Finset.sum_biUnion (BV_pairwiseDisjoint η _)]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun τ _ => leafProduct_digitsT encA encB τ)
    (Finset.sum_congr rfl fun V hV => Finset.sum_congr rfl fun π hπ => ?_)
  rw [storedD, dpValueD_digitsC, card_starLevels]

end ThreeSumApsp.Spec
