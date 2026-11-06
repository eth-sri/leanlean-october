/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Brownian.Reflection.MassBlocks
import DOZZ.GMC.Moments.ExactScaleBallMoment
import DOZZ.GMC.Moments.SetMassMeasurable
import DOZZ.GMC.Moments.SubunitSet

/-! The exact first-moment scale law rules out an atom at the inversion chart's missing point. -/


open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Every finite-mass `IsGMCOf` version is almost surely atomless at the origin. The first moment
of a shrinking centered ball is its area scale times the fixed reference-ball first moment. -/
theorem gmc_atomless_at_zero_of_isGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∀ᵐ ω ∂P, M ω {0} = 0 := DOZZ.Proofs.equatorGFF_GMC_origin_null_ae P X hX γ hγ hγ2 M hM

end DOZZ.Proofs
