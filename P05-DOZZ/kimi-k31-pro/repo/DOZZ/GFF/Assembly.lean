/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.GFF.EquatorDistributionBridge

/-!
# DOZZ.GFF.Assembly

The samplewise distribution constructed from the concrete torus-box Fourier charts satisfies
the equator-GFF specification `DOZZ.IsEquatorGFF`.
-/


open MeasureTheory ProbabilityTheory
open scoped Distributions

namespace DOZZ.Proofs

/-- The white-noise probability space carries a measurable, distribution-valued equator GFF. Each
test evaluation has the centered Gaussian law with variance prescribed by the covariance
`gffCov`. -/
theorem isEquatorGFF_equatorGFFDistribution :
    IsEquatorGFF (GaussianFields.scaleSpaceWhiteNoiseMeasure 2)
      equatorGFFDistribution := by
  refine ⟨inferInstance, fun f => ?_⟩
  refine ⟨measurable_equatorGFFDistribution_apply f, ?_⟩
  refine ⟨Real.toNNReal (gffCov f f), ?_, ?_⟩
  · exact Real.coe_toNNReal _ (gffCov_self_nonneg f)
  · rw [Measure.map_congr (ae_equatorGFFDistribution_apply_eq_equatorFieldL2 f)]
    exact map_equatorFieldL2_eq_gaussianReal f

end DOZZ.Proofs

