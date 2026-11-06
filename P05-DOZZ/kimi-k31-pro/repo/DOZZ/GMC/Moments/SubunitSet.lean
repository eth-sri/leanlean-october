/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.GMC.GmcMassMoment
import DOZZ.GMC.Moments.SubunitLimit

/-! Subunit moments of arbitrary GMC masses, localized by measure monotonicity. -/


open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Every measurable or nonmeasurable set mass is bounded in subunit moment by the total mass;
the measure-mono argument is pointwise and does not require measurability of the set evaluation. -/
theorem gmc_mass_subunit_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (O : Set ℂ)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    gmcMassMoment P M O p ≤ 1 + gmcReferenceMeasure Set.univ := by
  unfold gmcMassMoment
  calc
    ∫⁻ ω, ENNReal.rpow (M ω O) p ∂P ≤
        ∫⁻ ω, ENNReal.rpow (M ω Set.univ) p ∂P := by
          apply lintegral_mono
          intro ω
          exact ENNReal.rpow_le_rpow (measure_mono (Set.subset_univ O)) hp0
    _ ≤ 1 + gmcReferenceMeasure Set.univ :=
      gmc_total_mass_subunit_moment_bound P X hX γ M hM hp0 hp1

end DOZZ.Proofs
