module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.IsRCInfiniteVolumeLimit
public import PottsDiscontinuity.Frozen.Defs.RCCriticalParameter
public import PottsDiscontinuity.Frozen.Defs.RCInfiniteOpenGraph
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.RCMProof.Item3

/-! # Proof of Theorem 1.2, items 1–3 and (1.2) (`rc_theorem_1_2`) -/

@[expose] public section

namespace PottsDiscontinuity.Provider

open MeasureTheory Filter Topology Real

/-- Theorem 1.2, items 1–3 and (1.2), in the form used to close the statement `rc_theorem_1_2`. -/
theorem rc_theorem_1_2 {q : ℝ} (hq : 4 < q := by assumption) :
    ∃ φ : Fin 2 → Measure (squareLattice.edgeSet → Bool),
      (∀ i, IsRCInfiniteVolumeLimit (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
        ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i (φ i)) ∧
      φ 1 ≠ φ 0 ∧
      (φ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
            atTop (𝓝 (lam + 2 * S))) :=
  RCMProof.rc_theorem_1_2_assembled q hq

end PottsDiscontinuity.Provider
