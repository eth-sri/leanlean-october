module
public import GuthMaynard.AffineSource.LargeValuesAffineIteration
public import DensityEnergyGM.LargeValuesAffine

@[expose] public section

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology

namespace GuthMaynard.NativeMoment

/- Shared affine-analysis implementation; the original namespace is retained through aliases. -/
export RiemannZeta.GuthMaynard (
  GMAffineIterationSupported
  GMAffineSourceSupported
  GMAffineSupportedOn
  GMAffineSupportedOn.mono
  exists_global_card_gmAffineFirstPoissonPairs_middle_real_le
  exists_nat_mul_ge_of_pos
  gmAffineFirstPoissonRadius
  gmAffineFirstPoissonRadius_card_factor_mul_scale_le
  gmAffineFirstPoissonRadius_le_of_scale
  gmAffineIterationEta
  gmAffineIterationEta_le_one
  gmAffineIterationEta_pos
  gmAffineIterationQ_cube_le
  gmAffineIterationQ_mul_M_le_four_Y
  gmAffineIterationRegionIIScaleFactor_le
  gmAffinePoissonEnvelopes_le_mass
  gmAffineRegionIConstant
  gmAffineRegionIICoreConstant
  gmAffineRegionIICoreConstant_nonneg
  gmAffineRegionIICoreRawBound
  gmAffineRegionIIIKernelConstant
  gmAffineRegionIIIRawBound
  gmAffineRegionIIIRawBound_le_source
  gmAffineRegionIIRawBound
  gmAffineRegionIIRawBound_eq_core_add_tail
  gmAffineRegionIITailMassConstant
  gmAffineRegionIITailMassConstant_nonneg
  gmAffineRegionIITailRawBound
  gmAffineRegionIITailRawBound_le_source
  gmAffineSecondPoissonCutoff
  gmAffineSecondPoissonCutoff_ge_Q
  gmAffineSecondPoissonCutoff_pos
  gmAffineSecondPoissonCutoff_width
  gmAffineSecondPoissonSmoothingScale_ge
  gmAffineTildeSchwartz_apply_sub
  gmAffineTildeSchwartz_supportedOn
  gmAffineTildeSchwartz_weighted_norms_le_sixteen
  integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_sigmaIIReal_add_source_tails_of_constants
  integral_gmAffineTildeSchwartz_le
  integral_gmAffineTildeSchwartz_sq_le
  norm_gmAffineSigmaIIReal_le_J_add_far
  ofReal_norm_finset_sum_sq_expand
  one_le_rpow_gmAffineIterationEta
  seminorm_fourier_gmAffineComplexify_le_integral
)

/-- The source affine functional is nonnegative at every nonempty scale. -/
theorem gmAffineJ_nonneg
    (f : ℝ → ℝ) {M : ℕ} (hM : 0 < M) : 0 ≤ gmAffineJ f M := by
  obtain ⟨M₁, M₂, M₃, _hscale, hEq⟩ :=
    exists_gmAffineTransformIntegral_eq_J f hM
  rw [← hEq]
  exact integral_nonneg fun _ => sq_nonneg _


end GuthMaynard.NativeMoment
