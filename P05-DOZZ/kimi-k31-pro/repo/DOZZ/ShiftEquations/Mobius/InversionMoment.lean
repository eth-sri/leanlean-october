/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.GMC.Construction.RootedCircleMassLimit
import DOZZ.GMC.SharpMoments.WeightedScale
import DOZZ.Statements.GMC.CoulombMass
import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.Statements.Defs.IsEquatorGFF
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


open MeasureTheory Filter
open scoped ENNReal

namespace DOZZ.Proofs

/-- A positive finite factor commutes with every real power. -/
theorem inversionMoment_mul_rpow {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (t : ℝ≥0∞)
    (q : ℝ) : (c * t) ^ q = c ^ q * t ^ q := DOZZ.Proofs.weightedScale_mul_rpow hc0 hct t q

/-- The equator chaos is almost surely atomless at every point. -/
theorem gmc_atomless_of_isGMCOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (x : ℂ) : ∀ᵐ ω ∂P, M ω {x} = 0 := DOZZ.Proofs.gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM x

end DOZZ.Proofs

