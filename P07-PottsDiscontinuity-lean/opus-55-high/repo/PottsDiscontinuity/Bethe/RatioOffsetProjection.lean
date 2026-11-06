module

public import PottsDiscontinuity.Bethe.RatioPredecessor

/-! # The canonical root projection recovers the source offset function -/

public section

open Set Finset

namespace PottsDiscontinuity.Bethe

section
variable {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
theorem ratio_rootIndex_before_first (hq : Monotone q) {x : ℝ} (hx : x < q ⟨0, hn⟩) :
    ratioRootIndex hn q x = ⟨0, hn⟩ := by
  have hs : (univ.filter (fun j => q j ≤ x)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hqj := (mem_filter.mp hj).2
    have hl := hq (show (⟨0, hn⟩ : Fin n) ≤ j by grind)
    linarith
  simp [ratioRootIndex, hs]

theorem ratio_rootIndex_after_last (_hq : Monotone q) {x : ℝ} (hx : q ⟨n - 1, by omega⟩ ≤ x) :
    ratioRootIndex hn q x = ⟨n - 1, by omega⟩ := by
  let s := univ.filter (fun j => q j ≤ x)
  let j : Fin n := ⟨n - 1, by omega⟩
  have hj : j ∈ s := by grind
  change (if h : s.Nonempty then s.max' h else ⟨0, hn⟩) = j
  rw [dite_eq_left (by grind)]
  apply le_antisymm
  · grind
  · exact Finset.le_max' s j hj
end

section
variable {n m : ℕ} (h : n = m) (hn : 0 < n) (hm : 0 < m) (q : Fin m → ℝ)
/-- An equality of root counts commutes with the canonical projection. -/
theorem ratio_rootIndex_cast (x : ℝ) :
    Fin.cast h (ratioRootIndex hn (fun j => q (Fin.cast h j)) x) = ratioRootIndex hm q x := by
  aesop

theorem ratio_root_mesh_cast {d : ℝ}
    (hmesh : ∀ j : Fin (m + 1),
      rootPartitionPoint m q hm j.succ - rootPartitionPoint m q hm j.castSucc ≤ d) :
    ∀ j : Fin (n + 1),
      rootPartitionPoint n (fun i => q (Fin.cast h i)) hn j.succ -
        rootPartitionPoint n (fun i => q (Fin.cast h i)) hn j.castSucc ≤ d := by
  aesop
end

section
variable {N r : ℕ}
/-- The finite source offset function is precisely the displacement of the
canonical predecessor, including both boundary half-cells. -/
theorem ratio_offsetFunction_eq_predecessor (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    (hn : 0 < N / 2 - r) (p : Fin (N / 2) → ℝ) (q : Fin (N / 2 - r) → ℝ)
    (hq : q ∈ S_n (N / 2 - r)) (x : ℝ) :
    offsetFunction N r h4 hr p q hn x =
      offsetDisplacement N r h4 hr p q (ratioRootIndex hn q x) := by
  by_cases hleft : x < q ⟨0, hn⟩
  · rw [ratio_rootIndex_before_first hn q hq.2.1.monotone hleft]
    simp_all [offsetFunction]
  by_cases hright : q ⟨N / 2 - r - 1, by omega⟩ ≤ x
  · rw [ratio_rootIndex_after_last hn q hq.2.1.monotone hright]
    simp_all [offsetFunction]
  obtain ⟨hj, hcell⟩ := ratio_rootIndex_cell hn q hq.2.1 (le_of_not_gt hleft) (lt_of_not_ge hright)
  exact offsetFunction_on_cell h4 hr hn hq.2.1 (ratioRootIndex hn q x) hj hcell

theorem ratio_alignedRoot_mem_Ioo (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} (hp : p ∈ S_n (N / 2)) (j : Fin (N / 2 - r)) :
    alignedRoot N r hr p j ∈ Ioo (-Real.pi) Real.pi := by
  unfold alignedRoot
  split
  · exact hp.1 _
  · constructor <;> linarith [(hp.1 ⟨j.val + (r - 1) / 2, by omega⟩).1,
      (hp.1 ⟨j.val + (r - 1) / 2, by omega⟩).2,
      (hp.1 ⟨j.val + (r + 1) / 2, by omega⟩).1,
      (hp.1 ⟨j.val + (r + 1) / 2, by omega⟩).2]
end

end PottsDiscontinuity.Bethe
