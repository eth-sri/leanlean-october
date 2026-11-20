module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Duality.Discontinuity
public import PottsDiscontinuity.Infra.Lambda

/-! # The free diagonal rate formula and its positivity -/

@[expose] public section

open MeasureTheory Filter Topology Real

namespace PottsDiscontinuity.RCMProof

/-- Item 3 of Theorem 1.2, uniformly for every free critical box limit. -/
def rcItem3ForEveryFreeLimit (q : ℝ) (hq : 4 < q) : Prop :=
  ∀ (μ : Measure (squareLattice.edgeSet → Bool)),
    IsRCInfiniteVolumeLimit
      (rcCriticalParameter ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩)
      ⟨q, lt_trans (by norm_num : (0 : ℝ) < 4) hq⟩ 0 μ →
  ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
    ∃ S : ℝ,
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
          (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
      Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
          Real.log (μ.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0)
            (diagonalSite n)})) atTop (𝓝 (lam + 2 * S))

theorem altTanhLimit_pos {lam S : ℝ} (hlam : 0 < lam)
    (hS : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S)) : 0 < lam + 2 * S := by
  obtain ⟨S₀, _, hS₀, _, hp, _⟩ := identity44 lam hlam
  rwa [tendsto_nhds_unique hS hS₀]

end PottsDiscontinuity.RCMProof
