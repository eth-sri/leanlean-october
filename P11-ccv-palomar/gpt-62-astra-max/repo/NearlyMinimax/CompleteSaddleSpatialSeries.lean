module

public import NearlyMinimax.CompleteSaddleEnergy
public import NearlyMinimax.HighWindowFactorialEnergy
public import NearlyMinimax.HighUnionRawFisher


@[expose] public section

/-! Exact finite-window accounting for the concrete saddle envelope. The
full source series has the factor 3^d k^d and the proved actual factorial
energy budget. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ}

theorem completeSaddleSpatialSeries_eq (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n : ℕ)
    [NeZero (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω n)] :
    let grid := lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n
    highSourceSpatialSeries d (grid) n C.densityLower Q.c
      (fun _j => completeSaddleGeometryEnvelope Q Cfr cf Cω n) =
    (3^d : ℕ)*(grid)^d *
      (∑ r ∈ Finset.range (n+1), poissonCountWeight
        (completeSaddleScoreFactor Q*completeSaddleMu C Cω n) r *
        ∫ u, completeSaddleGeometryEnvelope Q Cfr cf Cω n r u ∂fullSpatialPatchDesign d r) := by
  intro grid
  let k := grid
  have hparameter : n*highFixedScoreDenominator C.densityLower Q.c*(2/k)^d =
      completeSaddleScoreFactor Q*completeSaddleMu C Cω n :=
    high_design_factorial_parameter (highFixedScoreDenominator C.densityLower Q.c) (by
      simp [completeSaddleMu, lowerSaddleMu, lowerSaddleH] <;> ring)
  simp [highSourceSpatialSeries]
  grind [poissonCountWeight, fullSpatialPatchDesign]

theorem eventually_completeSaddleSpatialSeries_le [NeZero d]
    {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C)
    (hs : 1 < C.smoothness) (hd : 4*C.smoothness < d)
    {cf : ℝ} (hcf : 0 < cf) (Cfr Cω : ℝ) :
    let grid := lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
    ∀ᶠ n : ℕ in atTop,
      ∀ hk0 : NeZero (grid n),
      highSourceSpatialSeries d (grid n) n C.densityLower Q.c
        (fun _j => completeSaddleGeometryEnvelope Q Cfr cf Cω n) ≤
      (3^d : ℕ)*(grid n)^d *
          completeSaddleEnergyBudget Q Cfr cf Cω n := by
  filter_upwards [eventually_completeSaddleGeometry_factorial Q hs hd hcf Cfr Cω] with n hn
  intro hk0
  letI := hk0
  rw [completeSaddleSpatialSeries_eq]
  bound

end NearlyMinimax
