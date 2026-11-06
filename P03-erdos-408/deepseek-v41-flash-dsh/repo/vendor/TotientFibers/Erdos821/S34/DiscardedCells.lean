module

public import Erdos821.S34.FrameTasks
public import Erdos821.S34.BilinearBlocks

@[expose] public section

set_option autoImplicit false



namespace Erdos821.S34Core

theorem discarded_cell_mass {α κ : Type*} [Fintype α] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (ξ : ℝ) (hξ : 0 ≤ ξ) :
    (∑ x, if frameCellMass w cell (cell x) < ξ then w x else 0) ≤
      ((Finset.univ.image cell).card : ℝ) * ξ := by
  rw [Erdos821.S34.Proofs.sum_filter_partition Finset.univ cell]
  calc
    _ ≤ ∑ _ ∈ Finset.univ.image cell, ξ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : frameCellMass w cell j < ξ
      · calc
          _ = ∑ x ∈ Finset.univ.filter (fun x => cell x = j), w x := by
            apply Finset.sum_congr rfl
            intro x hx
            have heq := (Finset.mem_filter.mp hx).2
            simp [heq, hj]
          _ = frameCellMass w cell j := by rw [Finset.sum_filter]; rfl
          _ ≤ ξ := hj.le
      · have hz : (∑ x ∈ Finset.univ.filter (fun x => cell x = j),
            if frameCellMass w cell (cell x) < ξ then w x else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have heq := (Finset.mem_filter.mp hx).2
          simp [heq, hj]
        rw [hz]
        exact hξ
    _ = _ := by simp

end Erdos821.S34Core
