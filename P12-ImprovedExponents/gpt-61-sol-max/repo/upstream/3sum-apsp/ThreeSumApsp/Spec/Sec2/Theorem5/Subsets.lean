/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Util.Types
public import Mathlib.Data.Bool.Count
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The subsets of size `m` of `{1, …, L}`, enumerated

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  A subset is a *mask*: the list of `L` truth values saying
which levels belong to it, level 1 first (`maskSet`, `maskOf`).  The subsets of size `m` are
enumerated with those containing level 1 first, and so on recursively: `unrank L m r` is number `r`
in this order.

* The masks `unrank L m r` with `r < (L choose m)` have length `L` and `m` entries `true`, and they
  are distinct, because `rank` recovers `r` (`length_unrank`, `count_unrank`, `rank_unrank`).  So
  their sets of levels are distinct subsets of size `m` (`card_maskSet_unrank`,
  `eq_of_maskSet_unrank_eq`).
* A program lists them in a table without arithmetic, each mask from the one before it: the first
  mask is `true^m false^{L-m}` (`unrank_zero`), and two consecutive masks are
  `pre true false false^a true^b` and `pre false true true^b false^a` (`unrank_succ_shape`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The enumeration -/

/-- The mask number `r` (counted from 0) among the masks of length `L` with `m` entries `true`. -/
def unrank : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | L + 1, 0, _ => false :: unrank L 0 0
  | L + 1, m + 1, r =>
    if r < L.choose m then true :: unrank L m r else false :: unrank L (m + 1) (r - L.choose m)

/-- The position of a mask in the enumeration.  A mask that begins with `false` comes after all the
masks with the same number of entries `true` that begin with `true`; if the rest `l` of the mask has
`k > 0` entries `true`, there are `(|l| choose k - 1)` of them. -/
private def rank
  | [] => 0
  | true :: l => rank l
  | false :: l => (if l.count true = 0 then 0 else l.length.choose (l.count true - 1)) + rank l

/-- A mask of the enumeration has length `L`. -/
@[simp] theorem length_unrank L m r : (unrank L m r).length = L := by
  fun_induction unrank L m r <;> simp [*]

/-- A mask of the enumeration has `m` entries `true`. -/
theorem count_unrank {L m r} (hr : r < L.choose m) : (unrank L m r).count true = m := by
  -- Along the recursion of `unrank`; by Pascal's rule the number passed on is again in range.
  fun_induction unrank L m r <;> grind [Nat.choose_succ_succ']

/-- A mask of the enumeration has `L - m` entries `false`. -/
theorem count_false_unrank {L m r} (hr : r < L.choose m) :
    (unrank L m r).count false = L - m := by
  grind [count_unrank, length_unrank]

/-- `rank` undoes `unrank`. -/
private theorem rank_unrank {L m r} (hr : r < L.choose m) : rank (unrank L m r) = r := by
  fun_induction unrank L m r with
  | case1 m r =>
    -- No levels: the only mask is the empty one, and `r = 0`.
    cases m <;> simp_all [rank]
  | case2 L r ih =>
    -- The empty set: the only mask has no entry `true`, and `r = 0`.
    simp_all [rank, count_unrank]
  | case3 L m r h ih =>
    -- Level 1 belongs to the set.
    simpa [rank] using ih h
  | case4 L m r h ih =>
    -- Level 1 does not belong to the set: the `(L choose m)` masks with level 1 come before.
    rw [Nat.choose_succ_succ'] at hr
    have hrest : r - L.choose m < L.choose (m + 1) := by omega
    simp only [rank, count_unrank hrest, length_unrank, ih hrest, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel]
    omega

/-- Different numbers give different masks. -/
private theorem eq_of_unrank_eq {L m r r'} (hr : r < L.choose m) (hr' : r' < L.choose m)
    (h : unrank L m r = unrank L m r') : r = r' := by
  grind [rank_unrank]

/-! ## Masks and sets of levels -/

/-- The set of levels of a mask. -/
def maskSet L (mask : List Bool) : Finset (Fin L) :=
  Finset.univ.filter fun ℓ => mask.getD ℓ false

/-- The mask of a set of levels. -/
def maskOf {L} (Q : Finset (Fin L)) := List.ofFn fun ℓ => decide (ℓ ∈ Q)

/-- The mask of a set of levels has one entry for each level. -/
theorem length_maskOf {L} (Q : Finset (Fin L)) : (maskOf Q).length = L := by
  simp [maskOf]

/-- The entry of the mask at a level says whether the level belongs to the set. -/
theorem getD_maskOf {L n} Q (hn : n < L) :
    (maskOf Q).getD n false = decide (⟨n, hn⟩ ∈ Q) := by
  simp [maskOf, hn]

/-- The number of levels of a mask is the number of its entries `true`. -/
private theorem card_maskSet {L} mask (h : mask.length = L) :
    (maskSet L mask).card = mask.count true := by
  induction mask generalizing L with
  | nil =>
    subst h
    simp [maskSet]
  | cons x l ih =>
    -- Split off level 1.
    subst h

    ram_safe [maskSet, Fin.card_filter_univ_succ]

/-- The set of levels of a mask of the enumeration has `m` elements. -/
theorem card_maskSet_unrank {L m r} (hr : r < L.choose m) :
    (maskSet L (unrank L m r)).card = m := by
  grind [card_maskSet, length_unrank, count_unrank]

/-- The mask of the set of levels of a mask of length `L` is that mask. -/
theorem maskOf_maskSet {L} mask (h : mask.length = L) :
    maskOf (maskSet L mask) = mask := by
  ram_aesop [maskOf, maskSet]

/-- Different numbers give different sets of levels. -/
theorem eq_of_maskSet_unrank_eq {L m r r'} (hr : r < L.choose m) (hr' : r' < L.choose m)
    (h : maskSet L (unrank L m r) = maskSet L (unrank L m r')) : r = r' := by
  grind [eq_of_unrank_eq, maskOf_maskSet, length_unrank]

/-! ## From one mask to the next -/

/-- The first mask: `m` times `true`, then `L - m` times `false`. -/
theorem unrank_zero {L m} (hm : m ≤ L) :
    unrank L m 0 = List.replicate m true ++ List.replicate (L - m) false := by
  induction L generalizing m with
  | zero => aesop
  | succ L ih =>
    cases m with
    | zero => ram_arith [unrank, List.replicate_succ]
    | succ m =>
      have hm' := Nat.le_of_succ_le_succ hm
      simp [unrank, Nat.choose_pos hm', ih hm', List.replicate_succ]

/-- The last mask: `L - m` times `false`, then `m` times `true`. -/
private theorem unrank_last {L m} (hm : m ≤ L) :
    unrank L m (L.choose m - 1) = List.replicate (L - m) false ++ List.replicate m true := by
  induction L generalizing m with
  | zero => aesop
  | succ L ih =>
    cases m with
    | zero => grind [unrank]
    | succ m =>
      rcases Nat.lt_or_ge m L with hlt | hge
      · have  := Nat.choose_pos hlt


        rw [unrank, if_neg (by
          grind
        ), (by
          grind
         : (L + 1).choose (m + 1) - 1 - L.choose m = L.choose (m + 1) - 1), ih hlt, show L + 1 - (m + 1) = L - (m + 1) + 1 by omega]
        -- `replicate (a + 1) false` is `false :: replicate a false`.
        rfl
      · obtain rfl : m = L := by omega
        simpa [unrank, List.replicate_succ] using ih le_rfl

/-- Two consecutive masks of the enumeration: write the first one as
`pre ++ [true, false] ++ false^a ++ true^b`, with the last occurrence of `true, false`; then the
next one is `pre ++ [false, true] ++ true^b ++ false^a`. -/
theorem unrank_succ_shape {L m r} (hr : r + 1 < L.choose m) :
    ∃ (pre : List Bool) (a b : ℕ), L = pre.length + 2 + a + b ∧
      unrank L m r = pre ++ true :: false :: (List.replicate a false ++ List.replicate b true) ∧
      unrank L m (r + 1)
        = pre ++ false :: true :: (List.replicate b true ++ List.replicate a false) := by
  induction L generalizing m r with
  | zero => cases m <;> simp at hr
  | succ L ih =>
    cases m with
    | zero => simp at hr
    | succ m =>
      rw [Nat.choose_succ_succ'] at hr
      rcases Nat.lt_trichotomy (r + 1) (L.choose m) with hboth | hlast | hneither
      · -- Both masks contain the first level.
        grind [unrank]
      · -- The last mask with the first level, and the first one without it.
        have hmL : m + 1 ≤ L := by
          grind
        refine ⟨[], L - m - 1, m, by rw [List.length_nil]; omega, ?_, ?_⟩
        · rw [unrank, if_pos (by omega), show r = L.choose m - 1 by omega, unrank_last (by omega),
            show L - m = L - m - 1 + 1 by omega]
          rfl
        · rw [unrank, if_neg (by omega), hlast, Nat.sub_self, unrank_zero hmL, Nat.sub_sub]
          rfl
      · -- Neither mask contains the first level.
        obtain ⟨pre, a, b, hlen, hthis, hnext⟩ := ih (m := m + 1) (r := r - L.choose m) (by omega)
        refine ⟨false :: pre, a, b, by rw [List.length_cons]; omega, ?_, ?_⟩
        · simp_all [unrank]
        · ram_grind [unrank]

end ThreeSumApsp.Spec
