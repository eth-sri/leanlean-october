/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem17.Instances
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Theorem 17, third step: witnesses

For every query pair that the oracle accepts, the piece `C_k` of its instance is scanned for a `c`
with `S(a,b,c) = 0`, and the scans stop at the first zero triangle.  As in the paper:

* a zero triangle is always found (`TriangleInstance.exists_mem_acceptedPairs`);
* a failed scan contains a false positive of `p`
  (`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`), and distinct scans contain
  distinct false positives (`TriangleInstance.eq_of_mem_acceptedPairs`), so there are at most `F(p)`
  failed scans (`TriangleInstance.card_le_F_of_distinct_scans`,
  `TriangleInstance.card_failedScans_le`);
* a scan looks at at most `⌈s/g⌉ ≤ 2√D/g` vertices (`pieceSize_le_two_mul_sqrt_div`), so the scans
  cost `O((F(p) + 1)√D/g) = O(κ n³ log n/g)` (`TriangleInstance.F_add_one_mul_pieceSize_le`).

`Theorem17.correctness` puts the first two together.

The program for Theorem 17 works on lists, and for its lists the sentences of this step are lemmas
of their own: `HostData.found_m` answers `TriangleInstance.exists_mem_acceptedPairs`,
`HostData.exists_false_positive` answers
`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`, `HostData.Valid.eq_of_place_eq`
answers `TriangleInstance.eq_of_mem_acceptedPairs`, and `HostData.sum_fails_le` answers
`TriangleInstance.card_failedScans_le`.  The two proofs share `F(p)`, the first step of the
proof, the number of instances and the counting step `TriangleInstance.card_le_F_of_distinct_scans`;
no theorem about programs rests on another lemma of this file.
-/

@[expose] public section

namespace ThreeSumApsp

variable {n D g p : ℕ}

namespace TriangleInstance

variable {T : TriangleInstance ℤ n}

/-! ### Scans and accepted pairs -/

variable (T) (D g)

variable (p) (ans : InstanceIndex p → Fin n × Fin n → Bool)

variable {T D g p ans}

/-! ### The sentences of the paragraph "Witnesses" -/

/-- Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans", for any finite family `s` of scans and any notion "the scan `x` contains the triple
`t`".  The scans of the accepted pairs (`card_failedScans_le`) and the scans of the program
(`HostData.sum_fails_le`) are two such families. -/
theorem card_le_F_of_distinct_scans (T : TriangleInstance ℤ n) {σ : Type*} (s : Finset σ)
    (contains : σ → Fin n × Fin n × Fin n → Prop)
    (hfalse : ∀ x ∈ s, ∃ t, contains x t ∧ T.IsFalsePositive p t)
    (hdistinct : ∀ t, ∀ x ∈ s, ∀ y ∈ s, contains x t → contains y t → x = y) :
    s.card ≤ T.F p := by
  classical
  refine Finset.card_le_card_of_forall_subsingleton contains (fun x hx => ?_)
    fun t _ x hx y hy => hdistinct t x hx.1 y hy.1 hx.2 hy.2
  obtain ⟨t, ht, hfp⟩ := hfalse x hx
  exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfp⟩, ht⟩

end TriangleInstance

/-! ### The output of the reduction -/

end ThreeSumApsp
