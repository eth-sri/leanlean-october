module
public import GuthMaynard.AffineSource.LargeValuesAffineHeight
public import DensityEnergyGM.LargeValuesAffineIteration

@[expose] public section

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology

namespace GuthMaynard.NativeMoment

/- Shared affine-analysis implementation; the original namespace is retained through aliases. -/
export RiemannZeta.GuthMaynard (
  GMAffineHeightFourierMassBound
  GMAffineHeightFourierMassFamilyAtDepth
  exists_gmAffineHeightDecayConstant
  gmAffineRegionIIISourceBound_le_heightMass
  gmAffineRegionIITailSourceBound_le_heightMass
  gmAffineTildeSchwartz_heightFourierMassBound
  gmAffineTildeSchwartz_heightFourierMassFamilyAtDepth_succ
  gmAffine_proposition9_1_height_family_native
)


end GuthMaynard.NativeMoment
