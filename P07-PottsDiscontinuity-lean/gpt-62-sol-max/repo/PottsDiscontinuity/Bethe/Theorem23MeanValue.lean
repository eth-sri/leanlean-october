module

public import PottsDiscontinuity.Bethe.AsymptoticPartition
public import PottsDiscontinuity.Bethe.Theorem23Counting

/-! # Exact counting increments and cell mean values for Bethe solutions -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem betheCountingFunction_cell_increment {Δ : ℝ} {N k : ℕ} (hN : 0 < N)
    (p : Fin (k + 1) → ℝ) (hs : 2 * (k + 1) ≤ N)
    (hBE : DiscreteBetheEquation Δ N (k + 1) p) (j : Fin (k + 2)) :
    betheCountingFunction Δ N (k + 1) p (rootPartitionPoint (k + 1) p (by omega) j.succ) -
      betheCountingFunction Δ N (k + 1) p (rootPartitionPoint (k + 1) p (by omega) j.castSucc) =
        rootGapMultiplicity N (k + 1) j / (N : ℝ) := by
  simpa [← div_eq_mul_inv] using
      rootPartitionPoint_increment hs (betheCountingFunction Δ N (k + 1) p) (N : ℝ)⁻¹
        (fun i => by rw [← div_eq_mul_inv, betheCountingFunction_root_value hN p hBE])
        (fun x => by rw [← div_eq_mul_inv, betheCountingFunction_period hN p]) j

theorem exists_betheCountingDerivative_cell_mean {Δ : ℝ} (hΔ : Δ < -1)
    {N k : ℕ} (hN : 0 < N) (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
    (hs : 2 * (k + 1) ≤ N) (hBE : DiscreteBetheEquation Δ N (k + 1) p)
    (j : Fin (k + 2)) :
    ∃ ξ ∈ Ioo (rootPartitionPoint (k + 1) p (by omega) j.castSucc)
        (rootPartitionPoint (k + 1) p (by omega) j.succ),
      betheCountingDerivative Δ N (k + 1) p ξ = rootGapMultiplicity N (k + 1) j /
        ((N : ℝ) * (rootPartitionPoint (k + 1) p (by omega) j.succ -
          rootPartitionPoint (k + 1) p (by omega) j.castSucc)) := by
  have hgap := rootPartition_gap_pos hp (by omega) j
  have hcont :=
    continuous_iff_continuousAt.2 (fun x => (hasDerivAt_betheCountingFunction hΔ N (k + 1) p x).continuousAt)
  obtain ⟨ξ, hξ, hmean⟩ := exists_hasDerivAt_eq_slope
    (betheCountingFunction Δ N (k + 1) p) (betheCountingDerivative Δ N (k + 1) p)
    (sub_pos.mp hgap) hcont.continuousOn
    (fun x _ => hasDerivAt_betheCountingFunction hΔ N (k + 1) p x)
  refine ⟨ξ, hξ, ?_⟩
  rw [betheCountingFunction_cell_increment hN p hs hBE j] at hmean
  simpa [div_div] using hmean

end PottsDiscontinuity.Bethe
