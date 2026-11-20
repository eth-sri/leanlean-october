module

public import PottsDiscontinuity.Bethe.CountingStability

/-! # Mesh bootstrap for compact continuation -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The step-density error has a finite weighted supremum for every valid
configuration; boundedness is proved rather than imposed on solutions. -/
theorem rootStepDensity_error_bddAbove {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (p : Fin n → ℝ) (hn : 0 < n) :
    BddAbove (densityValues Δ (rootStepError Δ N p hn)) := by
  let c := fun j => rootGapMultiplicity N n j /
    ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc))
  let B := ∑ j, |c j|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hstep (x : ℝ) : |rootStepDensity N n p hn x| ≤ B := by
    unfold rootStepDensity
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    change |if _ then c j else 0| ≤ |c j|
    split_ifs
    · exact le_rfl
    simp
  obtain ⟨X, hX, hupper⟩ := exists_uniform_Xi_upper_bound hΔ
  obtain ⟨M, hρ⟩ := rho_uniform_upper_bound hΔ
  refine ⟨X * (B + M), ?_⟩
  rintro _ ⟨α, rfl⟩
  have hXi : |Xi (lamOf Δ) α| ≤ X := by
    rw [abs_of_pos (Xi_pos (lamOf_pos hΔ) _)]
    simp_all
  have hρabs : |rho Δ (kMap (lamOf Δ) α)| ≤ M := by
    rw [abs_of_pos (rho_pos hΔ _)]
    simp_all
  change |Xi (lamOf Δ) α * (rootStepDensity N n p hn (kMap (lamOf Δ) α) -
    rho Δ (kMap (lamOf Δ) α))| ≤ X * (B + M)
  rw [abs_mul]
  apply mul_le_mul hXi _ (abs_nonneg _) hX.le
  grind

end PottsDiscontinuity.Bethe
