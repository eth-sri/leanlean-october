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

theorem gmc_atomless_of_isGMCOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (x : ℂ) : ∀ᵐ ω ∂P, M ω {x} = 0 := by
  have hint := equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM {x} (measurableSet_singleton x)
  have href : gmcReferenceMeasure {x} = 0 := by
    unfold gmcReferenceMeasure
    simp
  rw [href] at hint
  have hmeas :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM {x} (measurableSet_singleton x)
  aesop

end DOZZ.Proofs

end
