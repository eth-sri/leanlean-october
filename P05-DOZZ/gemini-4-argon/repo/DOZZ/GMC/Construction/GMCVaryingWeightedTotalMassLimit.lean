/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCVaryingWeightedTotalMass
public import DOZZ.GMC.Construction.GMCWeightedTotalMass

/-! Convergence of total cutoff masses under uniformly varying weights. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private theorem tendstoInMeasure_add_of_sub
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {l} (f g : ι → Ω → ℝ) y
    (hfg : TendstoInMeasure P (fun i ω => f i ω - g i ω) l (fun _ => 0))
    (hgy : TendstoInMeasure P g l y) : TendstoInMeasure P f l y := by
  rw [tendstoInMeasure_iff_norm] at hfg hgy ⊢
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ≥0∞)) l (𝓝 0)) (by simpa using (show Tendsto (fun i => P {ω | δ ≤ ‖f i ω - g i ω‖}) l (𝓝 0) by simpa [δ, sub_zero] using hfg δ hδ).add (hgy δ hδ))
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [] with i
    calc
      P {ω | ε ≤ ‖f i ω - y ω‖} ≤
          P ({ω | δ ≤ ‖f i ω - g i ω‖} ∪ {ω | δ ≤ ‖g i ω - y ω‖}) := by
            apply measure_mono
            intro ω hω
            by_contra hnot
            rcases not_or.mp (by simpa only [Set.mem_union] using hnot) with ⟨h1, h2⟩
            have hsum : ‖f i ω - y ω‖ < ε := by
              calc
                ‖f i ω - y ω‖ = ‖(f i ω - g i ω) + (g i ω - y ω)‖ := by congr 1; ring
                _ ≤ ‖f i ω - g i ω‖ + ‖g i ω - y ω‖ := norm_add_le _ _
                _ < δ + δ := add_lt_add (lt_of_not_ge h1) (lt_of_not_ge h2)
                _ = ε := by dsimp [δ]; ring
            exact (not_le_of_gt hsum) hω
        _ ≤ P {ω | δ ≤ ‖f i ω - g i ω‖} + P {ω | δ ≤ ‖g i ω - y ω‖} := MeasureTheory.measure_union_le _ _

/-- For an `IsGMCOf` limit, the total cutoff mass under a uniformly convergent family of
nonnegative bounded-continuous weights converges in measure to the limit mass under the fixed
limiting weight. -/
theorem regularizedGMC_varyingWithDensity_univ_mass_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ) (hu : ∀ r z, 0 ≤ u r z)
    (v : BoundedContinuousFunction ℂ ℝ) (hv : ∀ z, 0 ≤ v z)
    (hconv : TendstoUniformly (fun r z => u r z) v atTop) :
    TendstoInMeasure P
      (fun r ω => (((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal) atTop
      (fun ω => ((M ω).withDensity
        (fun z => ENNReal.ofReal (v z)) Set.univ).toReal) := by
  let f : ℝ → Ω → ℝ := fun r ω => (((regularizedGMC P Xc γ r ω).withDensity
    (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal
  let g : ℝ → Ω → ℝ := fun r ω => (((regularizedGMC P Xc γ r ω).withDensity
    (fun z => ENNReal.ofReal (v z))) Set.univ).toReal
  let y : Ω → ℝ := fun ω => ((M ω).withDensity
    (fun z => ENNReal.ofReal (v z)) Set.univ).toReal
  simpa [f, y] using tendstoInMeasure_add_of_sub P f g y (by simpa [f, g] using regularizedGMC_varyingWithDensity_univ_mass_diff_tendstoInMeasure P X hX Xc hXc γ u hu v hv hconv) (by simpa [g, y] using regularizedGMC_withDensity_univ_mass_tendstoInMeasure P X hX Xc hXc γ M hM v hv)


end DOZZ.Proofs
