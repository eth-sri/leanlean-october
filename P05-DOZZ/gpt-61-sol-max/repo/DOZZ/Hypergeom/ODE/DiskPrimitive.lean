/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives

/-! Normalized holomorphic primitives on disks for the Picard construction. -/

@[expose] public section

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable (c : ℂ) (r : ℝ) (f : ℂ → E) (y : E) (hf : DifferentiableOn ℂ f (Metric.ball c r))

include c r f y hf in
/-- Choose the primitive of a holomorphic disk field normalized to have value `y` at `c`.
This is the primitive step used to define the local Picard iterates. -/
noncomputable def normalizedDiskPrimitive  : ℂ → E :=
  Classical.choose (hf.isExactOn_ball.with_val_at c y)

include c r f y hf in
theorem normalizedDiskPrimitive_apply_center  :
    normalizedDiskPrimitive c r f y hf c = y := (Classical.choose_spec (hf.isExactOn_ball.with_val_at c y)).1

theorem hasDerivAt_normalizedDiskPrimitive {c z : ℂ} {r : ℝ} {f : ℂ → E} {y : E}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (hz : z ∈ Metric.ball c r) :
    HasDerivAt (normalizedDiskPrimitive c r f y hf) (f z) z := (Classical.choose_spec (hf.isExactOn_ball.with_val_at c y)).2 z hz

include c r f y hf in
theorem differentiableOn_normalizedDiskPrimitive  :
    DifferentiableOn ℂ (normalizedDiskPrimitive c r f y hf) (Metric.ball c r) := by
  intro z hz
  exact (hasDerivAt_normalizedDiskPrimitive hf hz).differentiableAt.differentiableWithinAt

end DOZZ.Proofs
