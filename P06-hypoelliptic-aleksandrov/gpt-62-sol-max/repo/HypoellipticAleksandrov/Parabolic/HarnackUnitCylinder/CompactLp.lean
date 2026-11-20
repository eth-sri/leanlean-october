module

import HypoellipticAleksandrov.Analysis.CompactLp

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Finite-p membership on compactly contained open domains -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Set MeasureTheory
open scoped ENNReal

/-- Continuity on a neighborhood of a compact closure gives every restricted Lp bound. -/
theorem memLp_on_of_continuousOn_compact_closure
    {d : ℕ} {U V : Set (TimeVelocity d)} {f : TimeVelocity d → ℝ}
    (hf : ContinuousOn f U) (_hV : IsOpen V)
    (hcompact : IsCompact (closure V)) (hVU : closure V ⊆ U)
    (p : ℝ≥0∞) : MemLp f p (timeVelocityVolumeOn V) := 
  (Analysis.memLp_restrict_of_isCompact hcompact (hf.mono hVU) p).mono_measure
    (Measure.restrict_mono_set volume subset_closure)

end HypoellipticAleksandrov.Parabolic
