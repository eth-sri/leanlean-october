/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Step

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


namespace Light.Sec2

open Finset

namespace Encode

/- The local variables of encode: the arguments L, src, out, scr, tab, p7, p10; the lengths 7^{L-1}
and 10^{L-1}; the number of the term; the result of a call, which is not used. -/
slots Level Src Out Scr Table Pow7 Pow10 Len7 Len10 TermNo Res

end Encode

open Encode

/-- The two calls for one term: step (2) into the scratch area, and step (3) from there into the
part of the output that belongs to the term. -/
def encodeTerm (pS pE : ℕ) : Stmt :=
  .call pS [v Src, v Scr, v Len7, v TermNo, v Table] Res ;;
  .call pE [v Level -' k 1, v Scr, v Out +' v TermNo *' v Len10, v Scr +' v Len7, v Table, v Pow7,
    v Pow10] Res

/-- encode(L, src, out, scr, tab, p7, p10).  pS and pE are the numbers that the procedures encStep
and encode have in the program. -/
def encodeBody (pS pE : ℕ) : Stmt :=
  .ite (v Level =' k 0)
    (.store (v Out) (M (v Src)))
    (.set Len7 (M (v Pow7 +' v Level -' k 1)) ;;
     .set Len10 (M (v Pow10 +' v Level -' k 1)) ;;
     .for TermNo (k 10) (encodeTerm pS pE))

/-! ## What encode computes, how much room and how much time it needs -/

/-- The array A_lam of step (2), in terms of positions in arrays: a is the input array (7^{L+1}
numbers, seven slices of 7^L) and c the table of the coefficients (c (7 lam + s) is the coefficient
of slice number s in the term number lam). -/
def encSlice (c a : ℕ → ℤ) (L lam : ℕ) : ℕ → ℤ :=
  fun j => ∑ s ∈ range 7, c (7 * lam + s) * a (s * 7 ^ L + j)

/-- What encode computes, in terms of positions in arrays: a is the input array (7^L numbers), c the
table of the coefficients, and i < 10^L the position of a leaf. -/
def encIdx (c : ℕ → ℤ) : (L : ℕ) → (ℕ → ℤ) → ℕ → ℤ
  | 0, a, _ => a 0
  | L + 1, a, i => encIdx c L (encSlice c a L (i / 10 ^ L)) (i % 10 ^ L)

/-- The part of the encoding below the term number lam is the encoding of A_lam. -/
theorem encIdx_succ (c a : ℕ → ℤ) (L lam : ℕ) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c (L + 1) a (lam * 10 ^ L + i) = encIdx c L (encSlice c a L lam) i := by
  grind [encIdx, Nat.mul_add_div_of_lt, Nat.mul_add_mod_of_lt]

/-- The number of scratch cells that encode uses: 7^{L-1} + ⋯ + 7 + 1. -/
def scrSize : ℕ → ℕ
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
structure EncodePre (lim : Limits) (μ : ℕ → ℤ) (src out scr tab p7 p10 : ℕ) (V : ℤ) (L : ℕ)
    (a c : ℕ → ℤ) : Prop where
  lay : EncodeLayout lim src out scr tab p7 p10 L
  srcV : ∀ j < 7 ^ L, μ (src + j) = a j
  src_bound : ∀ j < 7 ^ L, -V ≤ a j ∧ a j ≤ V
  tabV : ∀ i < 70, μ (tab + i) = c i
  coef_bound : ∀ i < 70, -1 ≤ c i ∧ c i ≤ 1
  p7V : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)
  p10V : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ)
  word_bound : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word


variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' μ₁ μ₂ : ℕ → ℤ}
  {src out scr tab p7 p10 L lam : ℕ} {V : ℤ} {a c : ℕ → ℤ}

/-- The layout at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and `scrSize L`. -/
theorem EncodeLayout.places_succ (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1)) :
    tab + 70 ≤ out ∧ p7 + (L + 1) ≤ out ∧ p10 + (L + 1) ≤ out ∧ out + 10 * 10 ^ L ≤ src ∧
      src + 7 * 7 ^ L ≤ scr ∧ scr + (7 ^ L + scrSize L) ≤ lim.space ∧
      (lim.space : ℤ) ≤ lim.word ∧ (100 : ℤ) ≤ lim.word := by
  simpa [pow_succ', scrSize] using And.intro lay.tab_le <| And.intro lay.p7_le <|
    And.intro lay.p10_le <| And.intro lay.out_le <| And.intro lay.src_le <|
    And.intro lay.scr_le <| And.intro lay.std.space_le lay.std.const_le

/-- What has not changed at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and
`scrSize L`. -/
theorem sameOutside2_succ (h : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    SameOutside2 μ μ' out (10 * 10 ^ L) scr (7 ^ L + scrSize L) := by
  grind [scrSize]

/-- The layout of the recursive call for the term number `lam`: it reads the first `7^L` cells of
the scratch area, writes the part of the output below the term, and has the rest of the scratch
area. -/
theorem EncodeLayout.toRec (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1))
    (hlam : lam < 10) :
    EncodeLayout lim scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 L := by
  have hplaces := lay.places_succ
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  exact ⟨lay.std, by omega, by omega, by omega, by omega, by omega, by omega⟩

namespace EncodePre

/-- The bound `V` is not negative. -/
theorem V_nonneg (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) : 0 ≤ V := by
  have := pre.src_bound 0 (by positivity)
  omega

/-- In the course of `encode` at level `L + 1`, the hypotheses of `encStep` hold for every term. -/
theorem toStep (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c)
    (hlam : lam < 10) (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    EncStepPre lim μ' src scr (7 ^ L) lam tab V := by
  have hplaces := pre.lay.places_succ
  have hkept := sameOutside2_succ same
  have hword := pre.word_bound
  have hone : (1 : ℤ) ≤ 7 ^ L := by grind
  push_cast at hword
  exact
    ⟨pre.lay.std, by omega, by omega, by omega, fun i hi => by
        rw [Nat.add_assoc, hkept _ (by omega), pre.tabV _ (by omega)]
        exact pre.coef_bound _ (by omega), fun i hi => by
        rw [hkept _ (by omega), pre.srcV i (by omega)]
        exact pre.src_bound i (by omega), (mul_le_mul_of_nonneg_right (by omega) pre.V_nonneg).trans hword⟩

/-- After `encStep` has written `A_lam` to the scratch area, the hypotheses of `encode` hold at
level `L` for the recursive call. -/
theorem toRec (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hlam : lam < 10)
    (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1)))
    (hstep : ∀ j < 7 ^ L, μ₁ (scr + j) = encStepVal μ' src lam tab (7 ^ L) j 7)
    (same₁ : SameOutside μ' μ₁ scr (7 ^ L)) :
    EncodePre lim μ₁ scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 (7 * V) L
      (encSlice c a L lam) c := by
  have hplaces := pre.lay.places_succ
  have hkept := sameOutside2_succ same
  have hword := pre.word_bound
  have hsrc : ∀ j < 7 * 7 ^ L, μ' (src + j) = a j := fun j hj => by
    rw [hkept _ (by omega)]
    exact pre.srcV j (by omega)
  have htab : ∀ i < 70, μ' (tab + i) = c i := fun i hi => by
    rw [hkept _ (by omega)]
    exact pre.tabV i hi
  exact
    ⟨pre.lay.toRec hlam, fun j hj => by
        rw [hstep j hj]
        refine Finset.sum_congr rfl fun s hs => ?_
        grind [Nat.add_assoc, Nat.mul_add_lt_mul], fun j hj => by
        simpa [encSlice] using enc_sum_bound 7 fun s hs =>
          enc_coef_mul_bound (pre.coef_bound _ (by omega))
            (pre.src_bound _ (by simp_all [pow_succ', Nat.mul_add_lt_mul])), fun i hi => by rw [same₁ _ (by omega), htab i hi], pre.coef_bound, fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p7V i (by omega)], fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p10V i (by omega)], by
        rw [pow_succ'] at hword
        grind⟩

end EncodePre

/-! ## One term -/





variable {pS pE : ℕ}


/-! ## The recursion -/



      
