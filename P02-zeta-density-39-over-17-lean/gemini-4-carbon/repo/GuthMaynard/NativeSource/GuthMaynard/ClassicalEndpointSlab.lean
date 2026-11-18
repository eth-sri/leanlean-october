module
public import GuthMaynard.NativeSource.GuthMaynard.DFIDivisorEpsilon
public import GuthMaynard.NativeSource.GuthMaynard.Statements
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter Real Topology

namespace GuthMaynard.NativeMoment

theorem eventually_log_nat_power_le_rpow
    (B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, (Real.log T) ^ B ≤ T ^ η := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop (B : ℝ) hη).eventuallyLE, eventually_ge_atTop 1] with T hBound hT
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hT) _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_natCast] at hBound
  exact hBound

end GuthMaynard.NativeMoment
