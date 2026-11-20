/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Index

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

@[expose] public section

namespace ThreeSumApsp.Spec.ChanHeArray

open ChanHe Finset

/-- The remainders of the numbers of a list, as natural numbers. -/
def keys (M : ℕ) (L : List ℤ) : List ℕ := L.map fun x => (x % (M : ℤ)).toNat

/-- Each number has one remainder. -/
@[simp] theorem length_keys (M : ℕ) (L : List ℤ) : (keys M L).length = L.length := by simp [keys]

/-- The remainders are below `M`. -/
theorem keys_lt {M } (hM : 1 ≤ M) (L : List ℤ) : ∀ r ∈ keys M L, r < M := by
  intro r hr
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
  exact Int.toNat_emod_lt hM x

section
variable {M : ℕ}
  (hM : 1 ≤ M)
include hM

/-- The list of the remainders, as integers. -/
theorem map_cast_keys (L : List ℤ) :
    (keys M L).map (fun r : ℕ => (r : ℤ)) = L.map fun x => x % (M : ℤ) := by
  rw [keys, List.map_map]
  exact List.map_congr_left fun x _ => Int.natCast_toNat_emod hM x

/-- The size of a bucket is the number of times its remainder occurs in the list of the
remainders. -/
theorem card_bucket {L : List ℤ} (hL : L.Nodup) (r : ℕ) :
    #(bucket L.toFinset M r) = (keys M L).count r := by
  have hfilter : bucket L.toFinset M (r : ℤ) =
      (L.filter fun x => decide (x % (M : ℤ) = (r : ℤ))).toFinset := by
    simp [bucket]
  rw [hfilter, List.toFinset_card_of_nodup (hL.filter _), keys, List.count_eq_countP,
    List.countP_map, List.countP_eq_length_filter]
  congr 1
  refine List.filter_congr fun x _ => ?_
  have hcast := Int.natCast_toNat_emod hM x
  grind

end

end ThreeSumApsp.Spec.ChanHeArray
