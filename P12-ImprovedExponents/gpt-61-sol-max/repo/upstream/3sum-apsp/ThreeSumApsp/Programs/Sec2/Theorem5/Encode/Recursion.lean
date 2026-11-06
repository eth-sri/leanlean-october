/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Step

/-!
# The encoding of an array by the recursion of Section 2.4.1

"To compute it, we run Full with b left out and without step (4)" (Section 2.4.1).  If L = 0 the
leaf stores its number.  Otherwise, for each term λ, step (2) writes A_λ to a scratch area and the
recursive call of step (3) encodes it into the part of the output that belongs to the leaves below
λ.  The language has no division, so the lengths 7^{L-1} and 10^{L-1} of the parts are read from two
tables of powers.

`encIdx` is what `encode` computes, in terms of positions in arrays.  `encode` writes it to the
output within `encTime L = O(10^L)` steps (`encTime_le`), using `scrSize L` scratch cells.  The
proof is by induction on `L`:

* the hypotheses of `encode` at level `L + 1` give those of `encStep` (`EncodePre.toStep`) and,
  after it, those of the recursive call (`EncodePre.toRec`);
* the two calls for the term `λ` fill the part of the output below `λ` (`TermsDone.step`,
  `encodeTerm_spec`);
* `encode_leaf` is the case `L = 0`, `encode_node` the loop over the ten terms, and `encode_spec`
  the induction.
-/

@[expose] public section

namespace Light.Sec2

open Finset


/-! ## What encode computes, how much room and how much time it needs -/

/-- The array A_lam of step (2), in terms of positions in arrays: a is the input array (7^{L+1}
numbers, seven slices of 7^L) and c the table of the coefficients (c (7 lam + s) is the coefficient
of slice number s in the term number lam). -/
def encSlice (c a : Light.Memory) L lam :=
  fun j => ∑ s ∈ range 7, c (7 * lam + s) * a (s * 7 ^ L + j)

/-- What encode computes, in terms of positions in arrays: a is the input array (7^L numbers), c the
table of the coefficients, and i < 10^L the position of a leaf. -/
def encIdx (c : Light.Memory) : (L : ℕ) → Light.Memory → ℕ → ℤ
  | 0, a, _ => a 0
  | L + 1, a, i => encIdx c L (encSlice c a L (i / 10 ^ L)) (i % 10 ^ L)

/-- The number of scratch cells that encode uses: 7^{L-1} + ⋯ + 7 + 1. -/
def scrSize
  | 0 => 0
  | L + 1 => 7 ^ L + scrSize L

/-! ## The hypotheses -/

/-- Where the arrays of `encode` lie: the three tables, then the output, the input and the scratch
area, one behind the other. -/
structure EncodeLayout (lim : Limits) (src out scr tab p7 p10 L : ℕ) : Prop where
  std : Std lim
  tab_le : tab + 70 ≤ out
  p7_le : p7 + L ≤ out
  p10_le : p10 + L ≤ out
  out_le : out + 10 ^ L ≤ src
  src_le : src + 7 ^ L ≤ scr
  scr_le : scr + scrSize L ≤ lim.space

/-- The hypotheses of `encode`: the layout, what the cells hold, and how large the numbers are. -/
structure EncodePre (lim : Limits) (μ : Light.Memory) (src out scr tab p7 p10 : ℕ) (V : ℤ) (L : ℕ)
    (a c : Light.Memory) : Prop where
  lay : EncodeLayout lim src out scr tab p7 p10 L
  srcV : ∀ j < 7 ^ L, μ (src + j) = a j
  src_bound : ∀ j < 7 ^ L, -V ≤ a j ∧ a j ≤ V
  tabV : ∀ i < 70, μ (tab + i) = c i
  coef_bound : ∀ i < 70, -1 ≤ c i ∧ c i ≤ 1
  p7V : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)
  p10V : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ)
  word_bound : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' μ₁ μ₂ : Light.Memory}
  {src out scr tab p7 p10 L lam : ℕ} {V : ℤ} {a c : Light.Memory}

/-- The layout at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and `scrSize L`. -/
theorem EncodeLayout.places_succ (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1)) :
    tab + 70 ≤ out ∧ p7 + L + 1 ≤ out ∧ p10 + L + 1 ≤ out ∧ out + 10 * 10 ^ L ≤ src ∧
      src + 7 * 7 ^ L ≤ scr ∧ scr + (7 ^ L + scrSize L) ≤ lim.space ∧
      lim.space ≤ lim.word ∧ 100 ≤ lim.word := by
  ram_arith [pow_succ', scrSize]

/-- What has not changed at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and
`scrSize L`. -/
theorem sameOutside2_succ (h : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    SameOutside2 μ μ' out (10 * 10 ^ L) scr (7 ^ L + scrSize L) := by
  ram_arith [pow_succ', scrSize]

/-- The layout of the recursive call for the term number `lam`: it reads the first `7^L` cells of
the scratch area, writes the part of the output below the term, and has the rest of the scratch
area. -/
private theorem EncodeLayout.toRec (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1))
    (hlam : lam < 10) :
    EncodeLayout lim scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 L := by
  have  := lay.places_succ
  have  : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  exact ⟨lay.std, by omega, by omega, by omega, by omega, by omega, by omega⟩

namespace EncodePre

/-- The bound `V` is not negative. -/
private theorem V_nonneg (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) : 0 ≤ V := by
  ram_grind

variable (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c)
    (hlam : lam < 10) (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1)))

include pre hlam same in
/-- In the course of `encode` at level `L + 1`, the hypotheses of `encStep` hold for every term. -/
private theorem toStep  :
    EncStepPre lim μ' src scr (7 ^ L) lam tab V := by
  have  := pre.lay.places_succ
  have hkept := sameOutside2_succ same

  have hword := pre.word_bound
  have  : (1 : ℤ) ≤ 7 ^ L := one_le_pow₀ (by norm_num)
  rw [pow_succ'] at hword
  push_cast at hword
  exact
    { std := pre.lay.std, tab_le := by omega, src_le := by omega, dst_le := by omega
      coef := fun i hi => by
        rw [Nat.add_assoc, hkept _ (by omega), pre.tabV _ (by omega)]
        exact pre.coef_bound _ (by omega)
      vals := fun i hi => by
        rw [hkept _ (by omega), pre.srcV i (by rw [pow_succ']; omega)]
        exact pre.src_bound i (by rw [pow_succ']; omega)
      word_bound := (mul_le_mul_of_nonneg_right (by omega) pre.V_nonneg).trans hword }

include pre hlam same in
/-- After `encStep` has written `A_lam` to the scratch area, the hypotheses of `encode` hold at
level `L` for the recursive call. -/
private theorem toRec
    (hstep : ∀ j < 7 ^ L, μ₁ (scr + j) = encStepVal μ' src lam tab (7 ^ L) j 7)
    (same₁ : SameOutside μ' μ₁ scr (7 ^ L)) :
    EncodePre lim μ₁ scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 (7 * V) L
      (encSlice c a L lam) c := by
  have  := pre.lay.places_succ
  have hkept := sameOutside2_succ same

  have  : ∀ j < 7 * 7 ^ L, μ' (src + j) = a j := fun j hj => by
    rw [hkept _ (by omega)]
    exact pre.srcV j (by rw [pow_succ']; omega)
  have htab : ∀ i < 70, μ' (tab + i) = c i := fun i hi => by
    rw [hkept _ (by omega)]
    exact pre.tabV i hi
  exact
    { lay := pre.lay.toRec hlam
      srcV := fun j hj => by
        rw [hstep j hj]
        refine Finset.sum_congr rfl fun s hs => ?_
        grind [Nat.mul_add_lt_mul]
      src_bound := fun j hj => by
        simpa [encSlice] using enc_sum_bound 7 fun s hs =>
          enc_coef_mul_bound (pre.coef_bound (7 * lam + s) (by omega))
            (pre.src_bound (s * 7 ^ L + j) (by rw [pow_succ']; exact Nat.mul_add_lt_mul hs hj))
      tabV := fun i hi => by rw [same₁ _ (by omega), htab i hi]
      coef_bound := pre.coef_bound
      p7V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p7V i (by omega)]
      p10V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p10V i (by omega)]
      word_bound := by
        ram_safe }

end EncodePre

/-! ## One term -/

variable {pS pE : ℕ}

/-! ## The recursion -/

end Light.Sec2
