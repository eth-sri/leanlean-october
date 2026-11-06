module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Finite-p membership on compactly contained open domains -/

 public section

namespace HypoellipticAleksandrov.Parabolic

open Set MeasureTheory
open scoped ENNReal

/-- Continuity on a neighborhood of a compact closure gives every restricted Lp bound. -/
theorem memLp_on_of_continuousOn_compact_closure
    {d : ℕ} {U V : HypoellipticAleksandrov.Parabolic.Region d} {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hf : ContinuousOn f U) (hV : IsOpen V)
    (hcompact : IsCompact (closure V)) (hVU : closure V ⊆ U)
    (p : ℝ≥0∞) : MemLp f p (timeVelocityVolumeOn V) := by

  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (hf.mono hVU)

  letI : IsFiniteMeasure (timeVelocityVolumeOn V) := ⟨by
    simpa only [timeVelocityVolumeOn, Measure.restrict_apply_univ] using (lt_of_le_of_lt (measure_mono subset_closure) hcompact.measure_lt_top)⟩
  apply MemLp.of_bound ((hf.mono (subset_closure.trans hVU)).aestronglyMeasurable
    hV.measurableSet) C
  filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
  exact hC z (subset_closure hz)

end HypoellipticAleksandrov.Parabolic
