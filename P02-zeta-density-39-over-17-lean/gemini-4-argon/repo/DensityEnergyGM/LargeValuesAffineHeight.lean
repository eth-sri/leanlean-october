module
public import DensityEnergyGM.LargeValuesS3
public import GuthMaynard.AffineSource.LargeValuesAffineHeight

@[expose] public section

namespace GuthMaynard.NativeMoment

theorem gmCubicLocalBump_eq_native :
    RiemannZeta.GuthMaynard.gmCubicLocalBump = gmCubicLocalBump := rfl

@[simp] theorem gmAffineLocalBumpSchwartz_apply (x : ℝ) :
    RiemannZeta.GuthMaynard.gmAffineLocalBumpSchwartz x = (gmCubicLocalBump x : ℂ) := rfl

