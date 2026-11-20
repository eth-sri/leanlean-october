module

public import PottsDiscontinuity.Bethe.DiscreteCore

/-! # Symmetry and aligned roots for the offset displacement -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- The full configuration root, or the mean of the two roots, aligned with
an index of the deficient configuration in (2.13). -/
noncomputable def alignedRoot (N r : ℕ) (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (j : Fin (N / 2 - r)) : ℝ :=
  if r % 2 = 0 then p ⟨j.val + r / 2, by omega⟩
  else (p ⟨j.val + (r - 1) / 2, by omega⟩ +
    p ⟨j.val + (r + 1) / 2, by omega⟩) / 2

theorem ratio_alignedRoot_mem_Ioo {N r : ℕ} (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} (hp : p ∈ S_n (N / 2)) (j : Fin (N / 2 - r)) :
    alignedRoot N r hr p j ∈ Ioo (-Real.pi) Real.pi := by
  unfold alignedRoot
  split
  · exact hp.1 _
  · constructor <;> linarith [(hp.1 ⟨j.val + (r - 1) / 2, by omega⟩).1,
      (hp.1 ⟨j.val + (r - 1) / 2, by omega⟩).2,
      (hp.1 ⟨j.val + (r + 1) / 2, by omega⟩).1,
      (hp.1 ⟨j.val + (r + 1) / 2, by omega⟩).2]

theorem alignedRoot_mem_Icc {N r : ℕ} (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} (hp : p ∈ S_n (N / 2)) (j : Fin (N / 2 - r)) :
    alignedRoot N r hr p j ∈ Icc (-Real.pi) Real.pi :=
  Ioo_subset_Icc_self (ratio_alignedRoot_mem_Ioo hr hp j)

theorem alignedRoot_rev {N r : ℕ} (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} (hp : p ∈ S_n (N / 2)) (j : Fin (N / 2 - r)) :
    alignedRoot N r hr p (Fin.rev j) = -alignedRoot N r hr p j := by
  have hsym := hp.2.2
  unfold alignedRoot
  split
  next he =>
    have hi : (⟨(Fin.rev j).val + r / 2, by omega⟩ : Fin (N / 2)) =
        Fin.rev ⟨j.val + r / 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    rw [hi, hsym]
  next ho =>
    have hi : (⟨(Fin.rev j).val + (r - 1) / 2, by omega⟩ : Fin (N / 2)) =
        Fin.rev ⟨j.val + (r + 1) / 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    have hi' : (⟨(Fin.rev j).val + (r + 1) / 2, by omega⟩ : Fin (N / 2)) =
        Fin.rev ⟨j.val + (r - 1) / 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    rw [hi, hi', hsym, hsym]
    ring

end PottsDiscontinuity.Bethe
