/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.FourPoint.RootedPairMoments
import DOZZ.Statements.GMC.EquatorGFFRootedGMCIdentity
import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Rooting Coulomb inverse moments -/

open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A fixed Coulomb mass is a measurable functional of its measure. -/
theorem fusion_measurable_coulombMass {N : ℕ} (γ : ℝ) (α : Fin N → ℝ)
    (z : Fin N → ℂ) (αinf : ℝ) :
    Measurable (fun μ : Measure ℂ => coulombMass γ μ α z αinf) := DOZZ.Proofs.coulombMass_measure_measurable γ α z αinf

end DOZZ.Proofs
