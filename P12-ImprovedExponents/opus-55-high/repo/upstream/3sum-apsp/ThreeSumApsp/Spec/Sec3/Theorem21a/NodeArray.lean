/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import PaperStatements
import ThreeSumApsp.Util.Index

/-!
# The array of a node of the reduction after Chan and He, from lists

For Theorem 21(a), after [CH20, Theorem 5.1].  The one-array instance of a node of the reduction
from 3SUM to Convolution-3SUM (`ChanHe.Node.oneArray`) is
defined through the buckets of three finite sets.  A program has each set as a list without
repetitions, computes the list of the remainders (`keys`), and counts how often each remainder
occurs.  In these terms:

* the size of a bucket is the number of times its remainder occurs (`card_bucket`);
* a cell of `arr` holds the number with that remainder if the remainder occurs once
  (`arr_of_count_eq_one`), and the padding value otherwise (`arr_of_count_ne_one`, `arr_of_le`);
* the cells `4i`, `4i + 1`, `4i + 2`, `4i + 3` of `oneArray` hold a constant and cell `i` of the
  three arrays, each shifted (`oneArray_cells`).
-/


namespace ThreeSumApsp.Spec.ChanHeArray

open ChanHe Finset

/-- The remainders of the numbers of a list, as natural numbers. -/
def keys (M : ℕ) (L : List ℤ) : List ℕ := L.map fun x => (x % (M : ℤ)).toNat

variable {M : ℕ}

/-- Each number has one remainder. -/
@[simp] theorem length_keys (M : ℕ) (L : List ℤ) : (keys M L).length = L.length := by simp [keys]

/-- The remainders are below `M`. -/
theorem keys_lt (hM : 1 ≤ M) (L : List ℤ) : ∀ r ∈ keys M L, r < M := by
  intro r hr
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
  exact Int.toNat_emod_lt hM x

/-- The list of the remainders, as integers. -/
theorem map_cast_keys (hM : 1 ≤ M) (L : List ℤ) :
    (keys M L).map (fun r : ℕ => (r : ℤ)) = L.map fun x => x % (M : ℤ) := by
  grind [keys, List.map_map, List.map_congr_left, Int.natCast_toNat_emod]

variable {L : List ℤ}

/-- The size of a bucket is the number of times its remainder occurs in the list of the
remainders. -/
theorem card_bucket (hM : 1 ≤ M) (hL : L.Nodup) (r : ℕ) :
    #(bucket L.toFinset M r) = (keys M L).count r := by
  have hfilter : bucket L.toFinset M r =
      (L.filter fun x => decide (x % M = (r : ℤ))).toFinset := by
    aesop
  grind [List.toFinset_card_of_nodup, keys, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter, List.filter_congr, Int.natCast_toNat_emod]

/-- A cell whose remainder occurs once holds the number with that remainder. -/
theorem arr_of_count_eq_one (hM : 1 ≤ M) (hL : L.Nodup) (pd : ℤ) {j : ℕ}
    (hj : j < L.length) (hc : (keys M L).count (L[j] % (M : ℤ)).toNat = 1) :
    arr L.toFinset M pd (L[j] % (M : ℤ)).toNat = L[j] := by
  rw [arr, card_bucket hM hL, if_pos hc]
  rw [← card_bucket hM hL] at hc
  obtain ⟨a, ha⟩ := card_eq_one.1 hc
  have hmem : L[j] ∈ bucket L.toFinset M (L[j] % M).toNat := by
    grind [bucket, List.mem_toFinset, List.getElem_mem, Int.natCast_toNat_emod]
  simp_all

/-- A cell whose remainder does not occur exactly once holds the padding value. -/
theorem arr_of_count_ne_one (hM : 1 ≤ M) (hL : L.Nodup) (pd : ℤ) {r : ℕ}
    (hc : (keys M L).count r ≠ 1) : arr L.toFinset M pd r = pd := by
  simp_all [arr, card_bucket]

/-- The cells from `M` on hold the padding value. -/
theorem arr_of_le (hM : 1 ≤ M) (S : Finset ℤ) (pd : ℤ) {i : ℕ} (hi : M ≤ i) :
    arr S M pd i = pd := by
  have hempty : bucket S M i = ∅ := by
    rw [bucket, filter_eq_empty_iff]
    intro x _ hx
    have hlt : x % M < M := Int.emod_lt_of_pos _ (by omega)
    omega
  grind [arr]

/-- The four kinds of cells of the one-array instance of a node.  Here `6V + 4` is the number
`G = 3W + 1` for `W = 2V + 1`. -/
theorem oneArray_cells (ν : Node) (V i : ℕ) :
    ν.oneArray V (4 * i) = 10 * (6 * V + 4) ∧
      ν.oneArray V (4 * i + 1) = arr ν.S₁ ν.M (2 * V + 1) i + (6 * V + 4) ∧
      ν.oneArray V (4 * i + 2) = arr ν.S₂ ν.M (2 * V + 1) i + 3 * (6 * V + 4) ∧
      ν.oneArray V (4 * i + 3) = arrZ ν.S₃ ν.M V i + 4 * (6 * V + 4) := by
  have hcell : ∀ r < 4, (4 * i + r) % 4 = r ∧ (4 * i + r) / 4 = i := by omega
  have hzero : 4 * i % 4 = 0 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Node.oneArray, ChanHe.oneArray, arrXY, pad, hzero, hcell 1 (by norm_num),
      hcell 2 (by norm_num), hcell 3 (by norm_num)] <;> norm_num <;> ring
