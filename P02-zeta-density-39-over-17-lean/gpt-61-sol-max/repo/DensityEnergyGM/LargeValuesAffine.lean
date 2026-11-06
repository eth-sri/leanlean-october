module
public import GuthMaynard.AffineSource.LargeValuesAffine
public import DensityEnergyGM.LargeValuesS3
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Fourier.PoissonSummation

@[expose] public section

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology

namespace GuthMaynard.NativeMoment

/- Shared affine-analysis implementation; the original namespace is retained through aliases. -/
export RiemannZeta.GuthMaynard (
  continuous_gmAffineTransformSum
  exists_gmAffineTransformIntegral_eq_J
  gmAffineCentralShell
  gmAffineComplexify
  gmAffineComplexify_apply
  gmAffineHighFrequencyRegion
  gmAffineIndexSet
  gmAffineJ
  gmAffineJ_le_crude
  gmAffineLocalBumpDual
  gmAffineLocalBumpSchwartz
  gmAffineLocalBumpSchwartz_apply
  gmAffineLowFrequencyRegion
  gmAffineLowFrequencyRegion_eq_Icc
  gmAffineMiddleFrequencyRegion
  gmAffinePoissonFarEnvelope
  gmAffinePoissonMainEnvelope
  gmAffinePositiveShell
  gmAffinePositiveShell_ne_zero
  gmAffineScaleTriples
  gmAffineSignedShell
  gmAffineSignedShell_ne_zero
  gmAffineSmoothTransformSchwartz
  gmAffineTerm
  gmAffineTermSchwartz
  gmAffineTermSchwartz_apply
  gmAffineTermSchwartz_fourier
  gmAffineTildeSchwartz
  gmAffineTildeSchwartz_nonneg
  gmAffineTransformIntegral
  gmAffineTransformIntegral_le_J
  gmAffineTransformIntegral_le_crude
  gmAffineTransformIntegral_le_smooth_fourier
  gmAffineTransformSum
  gmAffineTransformSum_eq_indexSum
  gmAffineTransformSum_nonneg
  gmAffineTransformSum_sq_le
  integrableOn_gmAffineHighFrequencyRegion_abs_rpow
  integrable_gmAffineTerm_sq
  integral_gmAffineHighFrequencyRegion_abs_rpow
  integral_gmAffineHighFrequencyRegion_fourier_sq_le
  integral_gmAffineLowFrequencyRegion_fourier_sq_le
  integral_gmAffineSmoothTransform_fourier_sq_eq_regions
  measurableSet_gmAffineHighFrequencyRegion
  mem_gmAffineCentralShell
  mem_gmAffineIndexSet
  mem_gmAffinePositiveShell
  mem_gmAffineScaleTriples
  mem_gmAffineSignedShell
  volume_real_gmAffineLowFrequencyRegion
)




end GuthMaynard.NativeMoment
