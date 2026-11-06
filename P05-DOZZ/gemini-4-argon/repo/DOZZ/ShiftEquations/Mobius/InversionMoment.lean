/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CoulombMass
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.GMC.Moments.InversionLaw
import DOZZ.GMC.Construction.GMCIntensityAdapter

/-!
# Coulomb moments under inversion

The inversion `y ↦ 1/y` preserves the law of the equator chaos
(`DOZZ.equatorGFF_GMC_inversion_law`). It maps the Coulomb weight with finite nonzero roots `zₖ` and
no charge at infinity to the weight with roots `1/zₖ`, up to the constant `∏ₖ |zₖ|^{γαₖ}`, away from
the roots and the origin. The chaos is almost surely atomless at every point (its intensity has a
density), so the Coulomb masses agree almost surely and every real power moment transforms by the
corresponding power of that constant.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace DOZZ.Proofs

/-- A positive finite factor commutes with every real power. -/
theorem inversionMoment_mul_rpow {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (t : ℝ≥0∞)
    (q : ℝ) : (c * t) ^ q = c ^ q * t ^ q := by
  by_cases ht : t = 0
  · subst ht
    rcases lt_trichotomy q 0 with hq | hq | hq
    · rw [mul_zero, ENNReal.zero_rpow_of_neg hq, ENNReal.mul_top]
      exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hct).ne'
    · subst hq; simp
    · rw [mul_zero, ENNReal.zero_rpow_of_pos hq, mul_zero]
  · exact ENNReal.mul_rpow_of_ne_zero hc0 ht q

/-- The equator chaos is almost surely atomless at every point. -/
theorem gmc_atomless_of_isGMCOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) x : ∀ᵐ ω ∂P, M ω {x} = 0 := by
  have hint := equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM {x} (measurableSet_singleton x)
  rw [(show gmcReferenceMeasure {x} = 0 by unfold gmcReferenceMeasure; exact withDensity_absolutelyContinuous _ _ (measure_singleton x))] at hint
  exact (lintegral_eq_zero_iff' (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM {x} (measurableSet_singleton x))).1 hint

end DOZZ.Proofs

end
