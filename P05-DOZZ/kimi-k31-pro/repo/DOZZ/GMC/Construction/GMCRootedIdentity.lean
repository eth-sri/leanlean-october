/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Defs.RegularizedGMC
import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.Statements.GMC.GmcReferenceMeasure
import DOZZ.GMC.EquatorGFFCameronMartin
import DOZZ.GMC.CircleAverageLimits
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import DOZZ.GFFStructure.AnnularWeakLimit
import Mathlib.MeasureTheory.Measure.Prod

/-! The finite-cutoff rooted identity for functionals of the field coordinates. -/


open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The point-root covariance against a smooth test is a continuous function of the root. -/
theorem gffRootCovariance_continuous (f : TestFn) :
    Continuous (fun u : ℂ => gffRootCovariance u f) := by
  simpa [gffRootCovariance] using continuous_testKernelPotential f

end DOZZ.Proofs
