/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.LocalModeSubsequence
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# DOZZ.GFF.HaarCommonLimit

The common subsequence of finite Haar distributions has measurable coordinate limits on every
local torus Fourier mode. These limits represent the accepted G4 evaluations almost everywhere.
-/

@[expose] public section

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace DOZZ

/-- The fixed subsequence selected by the common local-mode convergence theorem. -/
noncomputable def equatorHaarCommonSubsequence : ℕ → ℕ :=
  Classical.choose equatorHaarPartial_exists_common_localMode_subseq


theorem ae_tendsto_equatorHaarCommonSubsequence_localModes :
    ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      ∀ i : GFFLocalModeIndex,
        Tendsto
          (fun n => equatorHaarPartialDistribution
            (GaussianFields.gaussianIndexTruncation
              (GaussianFields.HaarBasisIndex 3) (equatorHaarCommonSubsequence n))
            ω (gffLocalSobolevModeTest i))
          atTop
          (𝓝 (GaussianFields.scalarWhiteNoiseL2 3
            (equatorKernelLimitMap (gffLocalSobolevModeTest i)) ω)) :=
  (Classical.choose_spec equatorHaarPartial_exists_common_localMode_subseq).2

/-- The `n`th finite Haar evaluation along the common subsequence. -/
noncomputable def equatorHaarCommonPartialEval (f : TestFn) (n : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) : ℝ :=
  equatorHaarPartialDistribution
    (GaussianFields.gaussianIndexTruncation
      (GaussianFields.HaarBasisIndex 3) (equatorHaarCommonSubsequence n)) ω f

/-- The everywhere-defined limit of the common-subsequence scalar evaluations. -/
noncomputable def equatorHaarCommonEval (f : TestFn)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) : ℝ :=
  limUnder atTop (fun n => equatorHaarCommonPartialEval f n ω)
section
variable (f : TestFn)

theorem measurable_equatorHaarCommonPartialEval (n : ℕ) :
    Measurable (equatorHaarCommonPartialEval f n) := measurable_equatorHaarPartialDistribution_apply _ f

theorem measurable_equatorHaarCommonEval :
    Measurable (equatorHaarCommonEval f) := by
  have hstrong : ∀ n, StronglyMeasurable (equatorHaarCommonPartialEval f n) :=
    fun n => (measurable_equatorHaarCommonPartialEval f n).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hstrong).measurable

end

/-- Every local mode limit agrees almost everywhere with its G4 isonormal evaluation. -/
theorem ae_equatorHaarCommonEval_localMode (i : GFFLocalModeIndex) :
    equatorHaarCommonEval (gffLocalSobolevModeTest i) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      GaussianFields.scalarWhiteNoiseL2 3
        (equatorKernelLimitMap (gffLocalSobolevModeTest i)) := by
  filter_upwards [ae_tendsto_equatorHaarCommonSubsequence_localModes] with ω hω
  change limUnder atTop (fun n => equatorHaarPartialDistribution
      (GaussianFields.gaussianIndexTruncation
        (GaussianFields.HaarBasisIndex 3) (equatorHaarCommonSubsequence n))
      ω (gffLocalSobolevModeTest i)) = _
  rw [(hω i).limUnder_eq]
section
variable (R : ℕ)

/-- The cosine-coordinate limits are square summable almost everywhere on each local chart. -/
theorem ae_summable_equatorHaarCommonCosEval :
    ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      Summable fun k : Fin 2 → ℤ =>
        (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2 := by
  filter_upwards [(ae_summable_gffLocalCosSobolevModeEvaluation R),
    ae_all_iff.mpr (fun k => ae_equatorHaarCommonEval_localMode (R, Sum.inl k))]
    with ω hω heq
  have heq' (k : Fin 2 → ℤ) :
      equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω =
        GaussianFields.scalarWhiteNoiseL2 3
          (equatorKernelLimitMap (gffLocalCosSobolevModeTest R k)) ω := by
    tauto
  simp_all

/-- The sine-coordinate limits are square summable almost everywhere on each local chart. -/
theorem ae_summable_equatorHaarCommonSinEval :
    ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      Summable fun k : Fin 2 → ℤ =>
        (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2 := by
  filter_upwards [(ae_summable_gffLocalSinSobolevModeEvaluation R),
    ae_all_iff.mpr (fun k => ae_equatorHaarCommonEval_localMode (R, Sum.inr k))]
    with ω hω heq
  have heq' (k : Fin 2 → ℤ) :
      equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω =
        GaussianFields.scalarWhiteNoiseL2 3
          (equatorKernelLimitMap (gffLocalSinSobolevModeTest R k)) ω := by
    tauto
  simp_all

end

end DOZZ

end
