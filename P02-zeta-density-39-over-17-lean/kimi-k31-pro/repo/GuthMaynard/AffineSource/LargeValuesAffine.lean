module
public import DensityEnergyGM.LargeValuesAffine
public import GuthMaynard.AffineSource.Foundation
public import ModuleExport

@[expose] public section
namespace RiemannZeta.GuthMaynard

export_module DensityEnergyGM.LargeValuesAffine from GuthMaynard.NativeMoment

theorem measurableSet_gmAffineLowFrequencyRegion (X : ℝ) :
    MeasurableSet (gmAffineLowFrequencyRegion X) := by
  exact measurableSet_le continuous_abs.measurable measurable_const

end RiemannZeta.GuthMaynard
