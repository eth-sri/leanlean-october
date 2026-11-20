module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.DiagonalComparison
public import PottsDiscontinuity.Duality.WiredPercolation

/-! The discontinuity consequences of positive diagonal decay, including the
exact parameter/event form consumed by Theorem 1.2 items 1–2. Neither the
theorem-statement modules (`Frozen/`) nor the provider modules (`Provider/`) are imported. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK MeasureTheory Filter Topology
noncomputable section

/-- All four discontinuity consequences under an explicit full ℓ¹ decay bound. -/
theorem critical_discontinuity_of_exponential_decay (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    μ₀ (infiniteClusterAt 0) = 0 ∧ 0 < μ₁ (infiniteClusterAt 0) ∧
      μ₁ existsInfiniteCluster = 1 ∧ μ₁ ≠ μ₀ := by
  have := hμ₀.1
  have hμ₁dual : IsRCInfiniteVolumeLimit (dualParameters (criticalParameters q)).toP
      (dualParameters (criticalParameters q)).toQ 1 μ₁ := by
    simpa only [dualParameters_criticalParameters] using hμ₁
  have hfree : μ₀ (infiniteClusterAt 0) = 0 := by
    apply infiniteClusterAt_zero_of_exponential_decay μ₀ C c hc
    intro x
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ₀ _)]
    exact ENNReal.ofReal_le_ofReal (hdecay x)
  obtain ⟨hpos,hone⟩ := wired_percolation_of_free_decay (criticalParameters q) μ₀ μ₁ hμ₀ hμ₁dual C c hC hc hdecay
  exact ⟨hfree,hpos,hone,fun e => (e ▸ hpos).ne' hfree⟩

/-- The rate is taken along the exact frozen points
`diagonalSite n = (floor(n/2), floor(n/2))`, with normalization 1/n. -/
theorem critical_discontinuity_of_pos_diagonal_rate {q : Set.Ici (1 : ℝ)}
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ₁)
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
      Real.log (twoPoint μ₀ (diagonalSite n))) atTop (𝓝 L)) :
    μ₀ (infiniteClusterAt 0) = 0 ∧ 0 < μ₁ (infiniteClusterAt 0) ∧
      μ₁ existsInfiniteCluster = 1 ∧ μ₁ ≠ μ₀ := by
  obtain ⟨C,c,hC,hc,hb⟩ := free_exponential_decay_of_pos_diagonal_rate μ₀ hμ₀ L hL hrate
  exact critical_discontinuity_of_exponential_decay q μ₀ μ₁ hμ₀ hμ₁ C c hC.le hc hb

end
end PottsDiscontinuity.Duality
