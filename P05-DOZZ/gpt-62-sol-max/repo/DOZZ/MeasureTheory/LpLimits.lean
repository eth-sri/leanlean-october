/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Combining errors that tend to zero in `Lᵖ`. -/
@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

section
variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} {l : Filter I} {p : ℝ≥0∞}

theorem tendsto_eLpNorm_add_zero {f g : I → Ω → ℝ} (hp : 1 ≤ p)
    (hf : Tendsto (fun i => eLpNorm (f i) p P) l (𝓝 0))
    (hg : Tendsto (fun i => eLpNorm (g i) p P) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i + g i) p P) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using hf.add hg) (fun _ => bot_le) (fun _ => eLpNorm_add_le hp)

theorem tendsto_eLpNorm_smul_zero {c : I → ℝ} {f : Ω → ℝ}
    (hc : Tendsto c l (𝓝 0)) (hf : MemLp f p P) :
    Tendsto (fun i => eLpNorm (c i • f) p P) l (𝓝 0) := by
  simpa only [eLpNorm_const_smul, Function.comp_def, enorm_zero, zero_mul] using
    ENNReal.Tendsto.mul_const ((continuous_enorm.tendsto (0 : ℝ)).comp hc)
      (Or.inr hf.eLpNorm_ne_top)

end
end DOZZ.Proofs
