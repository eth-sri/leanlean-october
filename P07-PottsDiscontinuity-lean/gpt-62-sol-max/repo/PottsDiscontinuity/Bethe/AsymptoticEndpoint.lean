module

public import PottsDiscontinuity.Bethe.AsymptoticPartition

/-! # Fixed-rank roots approach the endpoints -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem root_distance_from_boundary {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) {d : ℝ}
    (hmesh : ∀ j : Fin (n + 1),
      rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤ d)
    (j : Fin n) :
    p j + Real.pi ≤ ((j.val : ℝ) + 1) * d ∧
      Real.pi - p j ≤ ((n - j.val : ℕ) : ℝ) * d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨hfirst, hlast, hgap⟩ := root_mesh_consequences hp hmesh
  have hmono : Monotone (fun i : Fin (k + 1) => (i.val : ℝ) * d - p i) :=
    Fin.monotone_iff_le_succ.mpr (fun i => by
      have := hgap i
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      linarith)
  have hleft := hmono (show (⟨0, by omega⟩ : Fin (k + 1)) ≤ j from by simp)
  have hright := hmono (show j ≤ (⟨k, by omega⟩ : Fin (k + 1)) from by change j.val ≤ k; omega)
  dsimp only at hleft hright
  simp only [Nat.cast_zero, zero_mul, zero_sub] at hleft
  have hz : (⟨0, hn⟩ : Fin (k + 1)) = 0 := Fin.ext (by simp)
  have hl : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [hz] at hleft
  rw [hl] at hright
  constructor
  · nlinarith only [hleft, hfirst]
  · rw [Nat.cast_sub (show j.val ≤ k + 1 by omega), Nat.cast_add, Nat.cast_one]
    nlinarith only [hright, hlast]

end PottsDiscontinuity.Bethe
