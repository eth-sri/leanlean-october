/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Recursion
public import ThreeSumApsp.Util.List
public import Mathlib.Data.Nat.Bitwise

/-!
# Theorem 21(a), the reduction of Chan and He: from n numbers to one-array Convolution-3SUM

We read the 3SUM of the paper as: three of `n` numbers, at different positions, sum to 0.  Its
Convolution-3SUM has one array (Section 1.2).  The proof of [CH20, Theorem 5.1] is
about three sets and three arrays.  This file passes from the one to the other by elementary
devices, which are not from that proof, and shows that the whole reduction, `instances`, is correct.

* Three distinct values.  The label of a number `x` in `[-U, U]` is `x + U`.  The labels of two
  distinct numbers differ in a binary digit, so splitting the set of values by two binary digits of
  the labels, in all possible ways, separates any three distinct values into three sets
  (`distinct_iff_split`).
* A repeated value.  A solution that repeats a value is `a, a, -2a` or `0, 0, 0`
  (`threeSum_iff_distinct_or_degenerate`), and two further three-set inputs detect these
  (`degenerate_iff`).
* Three arrays in one.  `oneArray` interleaves the three arrays and adds multiples of a large number
  `G`, which cancel only in equations `X i + Y j = Z (i + j)` (`oneArray_correct`).
* The whole reduction.  `IsInput` lists the three-set inputs.  There is a solution iff one of them
  has one (`threeSum_iff_exists_input`), each of them meets the hypotheses of `reduction_correct`
  (`IsInput.admissible`), and the nodes of the reduction are the nodes of their trees
  (`mem_allNodes_iff`).  With `reduction_correct` this gives `instances_correct`.  The number of
  instances, their entries and the count for the searches are bounded in `length_instances_le`,
  `abs_instances_le` and `scanPairs_le`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ## One set instead of three: three distinct values -/

section

variable {U : ℕ} {S : Finset ℤ}

/-- On `[-U, U]` the label of `x` is `x + U`. -/
private theorem lab_cast {x} (hx : |x| ≤ (U : ℤ)) : (lab U x : ℤ) = x + U :=
  Int.toNat_of_nonneg (by grind)

/-- The label of an element of `[-U, U]` has at most `Lam U` binary digits. -/
private theorem lab_lt {x} (hx : |x| ≤ (U : ℤ)) : lab U x < 2 ^ Lam U := by
  have := lab_cast hx
  have := (abs_le.mp hx).2
  exact (by omega : lab U x ≤ 2 * U).trans_lt (Nat.lt_pow_succ_log_self (by norm_num) _)

/-- The labels of two different elements of `[-U, U]` differ in one of their `Lam U` lowest binary
digits. -/
private theorem exists_testBit_lab_ne {x y} (hx : |x| ≤ (U : ℤ)) (hy : |y| ≤ (U : ℤ))
    (hne : x ≠ y) : ∃ β < Lam U, (lab U x).testBit β ≠ (lab U y).testBit β := by

  obtain ⟨β, hβ⟩ := Nat.exists_testBit_ne_of_ne (fun h => hne (by grind [lab_cast]) : lab U x ≠ lab U y)
  -- from digit `Lam U` on, all digits of both labels are 0
  refine ⟨β, lt_of_not_ge fun hΛ => hβ ?_, hβ⟩
  have hpow := Nat.pow_le_pow_right (n := 2) (by norm_num) hΛ
  rw [Nat.testBit_eq_false_of_lt ((lab_lt hx).trans_le hpow),
    Nat.testBit_eq_false_of_lt ((lab_lt hy).trans_le hpow)]

/-- Let `x + y + z = 0` in `S`.  If the label of `x` differs from those of `y` and `z` in digit `β`,
and `y ≠ z`, then one of the three-set inputs obtained by splitting `S` has a solution. -/
private theorem exists_split_of_testBit (h : Bdd U S) {x y z} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) {β} (hβ : β < Lam U) (hxy : (lab U y).testBit β = !(lab U x).testBit β)
    (hxz : (lab U z).testBit β = !(lab U x).testBit β) (hyz : y ≠ z) (hs : x + y + z = 0) :
    ∃ β < Lam U, ∃ β' < Lam U, ∃ v : Bool,
      HasSol (splitA U β v S) (splitB U β β' v false S) (splitB U β β' v true S) := by
  obtain ⟨β', hβ', hne⟩ := exists_testBit_lab_ne (h y hy) (h z hz) hyz
  refine ⟨β, hβ, β', hβ', (lab U x).testBit β, x, mem_filter.mpr ⟨hx, rfl⟩, ?_⟩
  cases hyβ' : (lab U y).testBit β'
  · exact ⟨y, mem_filter.mpr ⟨hy, hxy, hyβ'⟩,
      z, mem_filter.mpr ⟨hz, hxz, by simpa [hyβ'] using hne.symm⟩, hs⟩
  · exact ⟨z, mem_filter.mpr ⟨hz, hxz, by simpa [hyβ'] using hne.symm⟩,
      y, mem_filter.mpr ⟨hy, hxy, hyβ'⟩, by omega⟩

/-- A set has three distinct elements with sum 0 iff one of the `2 (Lam U)²` three-set inputs,
obtained by splitting it by two binary digits, has a solution.  This step is not from [CH20]. -/
theorem distinct_iff_split (h : Bdd U S) :
    (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a + b + c = 0) ↔
      ∃ β < Lam U, ∃ β' < Lam U, ∃ v : Bool,
        HasSol (splitA U β v S) (splitB U β β' v false S) (splitB U β β' v true S) := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hab, hbc, hac, hs⟩
    obtain ⟨β, hβ, hbit⟩ := exists_testBit_lab_ne (h a ha) (h b hb) hab
    -- in digit `β` the third element agrees with `b` or with `a`
    by_cases hcb : (lab U c).testBit β = (lab U b).testBit β
    · exact exists_split_of_testBit h ha hb hc hβ (Bool.eq_not_of_ne hbit.symm)
        (hcb.trans (Bool.eq_not_of_ne hbit.symm)) hbc hs
    · exact exists_split_of_testBit h hb ha hc hβ (Bool.eq_not_of_ne hbit)
        (Bool.eq_not_of_ne hcb) hac (by omega)
  · rintro ⟨β, -, β', -, v, a, ha, b, hb, c, hc, hs⟩
    obtain ⟨haS, haβ⟩ := mem_filter.mp ha
    obtain ⟨hbS, hbβ, hbβ'⟩ := mem_filter.mp hb
    obtain ⟨hcS, hcβ, hcβ'⟩ := mem_filter.mp hc
    grind

end

/-! ## Positions instead of values: solutions that repeat a value -/

section

variable {n : ℕ} {x : Fin n → ℤ}

/-- There is a solution that repeats a value: `a, a, -2a` with `a ≠ 0`, or `0, 0, 0`, at different
positions. -/
def Degenerate (x : Fin n → ℤ) :=
  (∃ a : ℤ, a ≠ 0 ∧ 2 ≤ #{i : Fin n | x i = a} ∧ ∃ k, x k = -2 * a) ∨ 3 ≤ #{i : Fin n | x i = 0}

/-- A solution at three different positions, two of which hold the same value, repeats a value. -/
private theorem degenerate_of_eq {i j k} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (he : x i = x j) (hs : x i + x j + x k = 0) : Degenerate x := by
  by_cases h0 : x i = 0
  · exact .inr (two_lt_card.mpr ⟨i, by simpa using h0, j, by simpa using he ▸ h0,
      k, by simp_all <;> omega, hij, hik, hjk⟩)
  · exact .inl ⟨x i, h0, one_lt_card.mpr ⟨i, by simp, j, by simp [he], hij⟩, k, by omega⟩

/-- Three different positions with sum 0: either the three values are distinct, or the solution
repeats a value. -/
theorem threeSum_iff_distinct_or_degenerate (x : Fin n → ℤ) :
    ThreeSum x ↔
      (∃ a ∈ univ.image x, ∃ b ∈ univ.image x, ∃ c ∈ univ.image x,
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a + b + c = 0) ∨ Degenerate x := by
  constructor
  · rintro ⟨i, j, k, hij, hjk, hik, hs⟩
    by_cases hxij : x i = x j
    · aesop (add safe apply [degenerate_of_eq])
    by_cases hxjk : x j = x k
    · exact .inr (degenerate_of_eq hjk hij.symm hik.symm hxjk (by omega))
    by_cases hxik : x i = x k
    · exact .inr (degenerate_of_eq hik hij hjk.symm hxik (by omega))
    · ram_grind
  · rintro (⟨a, ha, b, hb, c, hc, hab, hbc, hac, hs⟩ | ⟨a, ha0, h2, k, hk⟩ | h3)
    · obtain ⟨i, -, rfl⟩ := mem_image.mp ha
      obtain ⟨j, -, rfl⟩ := mem_image.mp hb
      obtain ⟨k, -, rfl⟩ := mem_image.mp hc
      exact ⟨i, j, k, fun e => hab (e ▸ rfl), fun e => hbc (e ▸ rfl), fun e => hac (e ▸ rfl), hs⟩
    · obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp h2
      simp only [mem_filter, mem_univ, true_and] at hi hj
      have hne : ∀ t , x t = a → t ≠ k := by
        rintro t ht rfl
        omega
      exact ⟨i, j, k, hij, hne j hj, hne i hi, by omega⟩
    · obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := two_lt_card.mp h3
      simp only [mem_filter, mem_univ, true_and] at hi hj hk
      exact ⟨i, j, k, hij, hjk, hik, by omega⟩

/-- There is a solution that repeats a value iff one of two three-set inputs has a solution.  The
first input leaves the search for `-2a` to the reduction.  The second already contains the answer
for `0, 0, 0`; see `zeroSet`. -/
theorem degenerate_iff (x : Fin n → ℤ) :
    Degenerate x ↔ HasSol (twiceSet x) {0} (univ.image x) ∨ HasSol (zeroSet x) {0} {0} := by
  refine or_congr ⟨?_, ?_⟩ ⟨fun h3 => ?_, ?_⟩
  · rintro ⟨a, ha0, h2, k, hk⟩
    obtain ⟨i, hi, -⟩ := one_lt_card.mp h2
    have ha := mem_image.mpr ⟨i, mem_univ i, (mem_filter.mp hi).2⟩
    exact ⟨2 * a, mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, ha0, h2⟩, rfl⟩, 0, mem_singleton_self 0,
      x k, mem_image_of_mem x (mem_univ k), by omega⟩
  · rintro ⟨_, ha', b, hb, _, hc, hs⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
    obtain ⟨-, ha0, h2⟩ := mem_filter.mp ha
    obtain ⟨k, -, rfl⟩ := mem_image.mp hc
    rw [mem_singleton.mp hb] at hs
    exact ⟨a, ha0, h2, k, by omega⟩
  · ram_safe [zeroSet]
  · rintro ⟨a, ha, -⟩
    by_contra h3
    rw [zeroSet, if_neg h3] at ha
    exact notMem_empty a ha

end

/-! ## Three arrays in one -/

section

variable {N W : ℕ} {X Y Z : Light.Memory}

/-- The definition of `oneArray` with `G` written out. -/
private theorem oneArray_val W X Y Z u :
    oneArray W X Y Z u = if u % 4 = 1 then X (u / 4) + (3 * W + 1)
      else if u % 4 = 2 then Y (u / 4) + 3 * (3 * W + 1)
      else if u % 4 = 3 then Z (u / 4) + 4 * (3 * W + 1) else 10 * (3 * W + 1) := rfl

/-- A solution `(i, j)` of the three arrays gives the solution `(4i + 1, 4j + 2)` of the one
array. -/
private theorem oneArray_sol W {i j} (h : X i + Y j = Z (i + j)) :
    oneArray W X Y Z (4 * i + 1) + oneArray W X Y Z (4 * j + 2) =
      oneArray W X Y Z (4 * i + 1 + 4 * j + 2) := by
  ram_safe [oneArray_val]

variable (hX : ∀ i < N, |X i| ≤ (W : ℤ)) (hY : ∀ i < N, |Y i| ≤ (W : ℤ))
    (hZ : ∀ i < N, |Z i| ≤ (W : ℤ))

include hX hY hZ in
/-- A solution of the one array is a solution of the three arrays: the multiples of `G = 3W + 1`
cancel only if the two indices have the remainders 1 and 2 modulo 4. -/
private theorem convSol_of_oneArray  {u v} (huv : u + v < 4 * N)
    (h : oneArray W X Y Z u + oneArray W X Y Z v = oneArray W X Y Z (u + v)) :
    ConvSol N X Y Z := by
  have hW : ∀ i < N, (-W ≤ X i ∧ X i ≤ W) ∧ (-W ≤ Y i ∧ Y i ≤ W) ∧
      -W ≤ Z i ∧ Z i ≤ W :=
    fun i hi => ⟨abs_le.mp (hX i hi), abs_le.mp (hY i hi), abs_le.mp (hZ i hi)⟩
  have  := hW (u / 4) (by omega)
  have  := hW (v / 4) (by omega)
  have  := hW ((u + v) / 4) (by omega)
  simp only [oneArray_val] at h
  by_cases h12 : u % 4 = 1 ∧ v % 4 = 2
  · refine ⟨u / 4, v / 4, by omega, ?_⟩
    rw [show u / 4 + v / 4 = (u + v) / 4 by omega]
    omega
  by_cases h21 : u % 4 = 2 ∧ v % 4 = 1
  · refine ⟨v / 4, u / 4, by omega, ?_⟩
    rw [show v / 4 + u / 4 = (u + v) / 4 by omega]
    omega
  · split_ifs at h <;> omega

include hX hY hZ in
/-- **Three arrays to one**, of four times the length.  Here `W` bounds the entries of the three
arrays below `N`.  This step is not from [CH20]. -/
theorem oneArray_correct  : ConvSol N X Y Z ↔ ConvOne (4 * N) (oneArray W X Y Z) :=
  ⟨fun ⟨i, j, _, h⟩ => ⟨4 * i + 1, 4 * j + 2, by omega, oneArray_sol W h⟩,
    fun ⟨_, _, huv, h⟩ => convSol_of_oneArray hX hY hZ huv h⟩

include hX hY hZ in
/-- The entries of the one array have absolute value at most `30W + 10`. -/
theorem abs_oneArray_le  {u} (hu : u < 4 * N) :
    |oneArray W X Y Z u| ≤ 30 * (W : ℤ) + 10 := by
  grind [oneArray_val]

end

/-! ## The one-array instance of a node -/

section

variable {n U : ℕ} {ν : Node}

variable (b₁ : Bdd U ν.S₁) (b₂ : Bdd U ν.S₂) (b₃ : Bdd U ν.S₃)

include b₁ b₂ b₃ in
/-- The entries of the three arrays of a node are bounded by the number `2U + 1` with which its
one-array instance is built. -/
private theorem Node.abs_arr_le  :
    (∀ i, |arrXY ν.S₁ ν.M U i| ≤ (2 * U + 1 : ℕ)) ∧
      (∀ i, |arrXY ν.S₂ ν.M U i| ≤ (2 * U + 1 : ℕ)) ∧
      ∀ i, |arrZ ν.S₃ ν.M U i| ≤ (2 * U + 1 : ℕ) := by
  aesop (add safe apply [abs_arrXY_le, abs_arrZ_le])

include b₁ b₂ b₃ in
/-- The three-array instance of a node and its one-array instance have the same answer. -/
theorem Node.conv_iff_convOne  N :
    ν.Conv U N ↔ ConvOne (4 * N) (ν.oneArray U) :=
  let ⟨hX, hY, hZ⟩ := Node.abs_arr_le b₁ b₂ b₃
  oneArray_correct (fun i _ => hX i) (fun i _ => hY i) fun i _ => hZ i

include b₁ b₂ b₃ in
/-- The entries of the one-array instance of a node have absolute value at most `60U + 40`. -/
theorem Node.abs_oneArray_le  u :
    |ν.oneArray U u| ≤ 60 * (U : ℤ) + 40 := by
  obtain ⟨hX, hY, hZ⟩ := Node.abs_arr_le b₁ b₂ b₃
  refine (ChanHe.abs_oneArray_le (N := u + 1) (fun i _ => hX i) (fun i _ => hY i)
    (fun i _ => hZ i) (by omega)).trans_eq ?_
  push_cast
  ring

/-- `reduction_correct` with one-array instances, read at length `8 * mPar n U ^ 2`. -/
theorem reduction_correct_oneArray (hn : 1 ≤ n) {T₁ T₂ T₃}
    (h : Admissible n U T₁ T₂ T₃) :
    HasSol T₁ T₂ T₃ ↔
      ∃ ν ∈ reduction n U T₁ T₂ T₃, ConvOne (8 * mPar n U ^ 2) (ν.oneArray U) := by
  rw [reduction_correct hn le_rfl h, show 8 * mPar n U ^ 2 = 4 * (2 * mPar n U ^ 2) by ring]
  refine exists_congr fun ν => and_congr_right fun hν => ?_
  have hν' := h.of_mem hν
  exact Node.conv_iff_convOne hν'.bdd₁ hν'.bdd₂ hν'.bdd₃ _

end

/-! ## The three-set inputs of the whole reduction -/

section

variable {n U : ℕ} {x : Fin n → ℤ}

variable (hx : ∀ i, |x i| ≤ (U : ℤ))

include hx in
/-- The values of `x` are bounded by `2U`. -/
private theorem bdd_image  : Bdd (2 * U) (univ.image x) := by
  intro a ha
  obtain ⟨i, -, rfl⟩ := mem_image.mp ha
  exact (hx i).trans (by omega)

include hx in
/-- The elements of `twiceSet x` are bounded by `2U`. -/
theorem bdd_twiceSet  : Bdd (2 * U) (twiceSet x) := by
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
  grind

/-- The set `{0}` is bounded by anything. -/
theorem bdd_zero U : Bdd U {0} := by
  intro a ha
  rw [mem_singleton.mp ha, abs_zero]
  exact Nat.cast_nonneg U

/-- The set `zeroSet x` is bounded by anything. -/
theorem bdd_zeroSet U (x : Fin n → ℤ) : Bdd U (zeroSet x) := by
  unfold zeroSet
  split_ifs
  · exact bdd_zero U
  · exact fun a ha => absurd ha (notMem_empty a)

/-- `n` numbers have at most `n` values. -/
theorem card_image_univ_le (x : Fin n → ℤ) : #(univ.image x) ≤ n :=
  card_image_le.trans_eq (card_fin n)

/-- `twiceSet x` has at most `n` elements. -/
private theorem card_twiceSet_le (x : Fin n → ℤ) : #(twiceSet x) ≤ n :=
  card_image_le.trans ((card_filter_le _ _).trans (card_image_univ_le x))

/-- `zeroSet x` has at most one element. -/
private theorem card_zeroSet_le (x : Fin n → ℤ) : #(zeroSet x) ≤ 1 := by
  grind [zeroSet]

/-- The three-set inputs on which the whole reduction runs `reduction n (2 * U)`. -/
inductive IsInput (U : ℕ) (x : Fin n → ℤ) : Finset ℤ → Finset ℤ → Finset ℤ → Prop
  /-- The set of values, split by two binary digits: for the solutions with three distinct
  values. -/
  | split {β β' : ℕ} (hβ : β < Lam (2 * U)) (hβ' : β' < Lam (2 * U)) (v : Bool) :
    IsInput U x (splitA (2 * U) β v (univ.image x)) (splitB (2 * U) β β' v false (univ.image x))
      (splitB (2 * U) β β' v true (univ.image x))
  /-- For the solutions `a, a, -2a`. -/
  | twice : IsInput U x (twiceSet x) {0} (univ.image x)
  /-- For the solution `0, 0, 0`. -/
  | zero : IsInput U x (zeroSet x) {0} {0}

/-- A property holds for one of the three-set inputs iff it holds for one of the splittings or for
one of the two further inputs. -/
private theorem exists_isInput_iff (P : Finset ℤ → Finset ℤ → Finset ℤ → Prop) :
    (∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ P T₁ T₂ T₃) ↔
      (∃ β < Lam (2 * U), ∃ β' < Lam (2 * U), ∃ v : Bool,
        P (splitA (2 * U) β v (univ.image x)) (splitB (2 * U) β β' v false (univ.image x))
          (splitB (2 * U) β β' v true (univ.image x))) ∨
      P (twiceSet x) {0} (univ.image x) ∨ P (zeroSet x) {0} {0} := by
  constructor
  · rintro ⟨_, _, _, ⟨hβ, hβ', v⟩ | _ | _, h⟩
    · grind
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rintro (⟨β, hβ, β', hβ', v, h⟩ | h | h)
    · exact ⟨_, _, _, .split hβ hβ' v, h⟩
    · exact ⟨_, _, _, .twice, h⟩
    · exact ⟨_, _, _, .zero, h⟩

include hx in
/-- Three entries of `x` at different positions sum to 0 iff one of the three-set inputs has a
solution. -/
theorem threeSum_iff_exists_input  :
    ThreeSum x ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ HasSol T₁ T₂ T₃ := by
  rw [threeSum_iff_distinct_or_degenerate, distinct_iff_split (bdd_image hx), degenerate_iff,
    exists_isInput_iff]

/-- The nodes of the whole reduction are the nodes of the trees of the three-set inputs. -/
theorem mem_allNodes_iff {ν} :
    ν ∈ allNodes n U x ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ ν ∈ reduction n (2 * U) T₁ T₂ T₃ := by
  rw [exists_isInput_iff fun T₁ T₂ T₃ => ν ∈ reduction n (2 * U) T₁ T₂ T₃]
  simp [allNodes]

/-- Each three-set input has at most `n` elements in each set, of absolute value at most `2U`. -/
theorem IsInput.admissible (hn : 1 ≤ n) (hx : ∀ i, |x i| ≤ (U : ℤ)) {T₁ T₂ T₃}
    (h : IsInput U x T₁ T₂ T₃) : Admissible n (2 * U) T₁ T₂ T₃ := by
  have hb := bdd_image hx
  have hc := card_image_univ_le x
  have hc0 := hn
  cases h with
  | split hβ hβ' v =>
    exact ⟨(card_filter_le _ _).trans hc, (card_filter_le _ _).trans hc,
      (card_filter_le _ _).trans hc, hb.mono (filter_subset _ _), hb.mono (filter_subset _ _),
      hb.mono (filter_subset _ _)⟩
  | twice => exact ⟨card_twiceSet_le x, hc0, hc, bdd_twiceSet hx, bdd_zero _, hb⟩
  | zero => exact ⟨(card_zeroSet_le x).trans hn, hc0, hc0, bdd_zeroSet _ x, bdd_zero _, bdd_zero _⟩

end

/-! ## The whole reduction -/

/-- **Correctness of the whole reduction.**  Let `x` consist of `n ≥ 1` integers of absolute value
at most `U`.  Then three entries of `x` at different positions sum to 0 iff one of the instances,
read at length `8 * mPar n (2 * U) ^ 2`, has a solution. -/
def instances_correct n U hn x hx :=
  calc ThreeSum x
      ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ HasSol T₁ T₂ T₃ := threeSum_iff_exists_input hx
    _ ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ ∃ ν ∈ reduction n (2 * U) T₁ T₂ T₃,
          ConvOne (8 * mPar n (2 * U) ^ 2) (ν.oneArray (2 * U)) :=
        exists₃_congr fun _ _ _ => and_congr_right fun hT =>
          reduction_correct_oneArray hn (hT.admissible hn hx)
    _ ↔ ∃ ν ∈ allNodes n U x, ConvOne (8 * mPar n (2 * U) ^ 2) (ν.oneArray (2 * U)) :=
        ⟨fun ⟨T₁, T₂, T₃, hT, ν, hν, h⟩ => ⟨ν, mem_allNodes_iff.mpr ⟨T₁, T₂, T₃, hT, hν⟩, h⟩,
          fun ⟨ν, hν, h⟩ =>
            let ⟨T₁, T₂, T₃, hT, hν'⟩ := mem_allNodes_iff.mp hν
            ⟨T₁, T₂, T₃, hT, ν, hν', h⟩⟩
    _ ↔ ∃ y ∈ instances n U x, ConvOne (8 * mPar n (2 * U) ^ 2) y := by
        simp only [instances, List.mem_map, exists_exists_and_eq_and]

end ChanHe

end ThreeSumApsp
