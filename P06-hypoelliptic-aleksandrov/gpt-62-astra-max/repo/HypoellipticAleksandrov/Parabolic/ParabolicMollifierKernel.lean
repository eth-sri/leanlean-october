module

public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Native-norm parabolic mollifier kernels

This module constructs normalized smooth compactly supported kernels on the
time--velocity carrier.  Their balls use the inherited finite-product
norm; no Euclidean metric instance is introduced here.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

/-- The outer radius of the `n`th native-norm parabolic mollifier. -/
noncomputable def parabolicMollifierScale (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- A smooth bump with inner radius half of, and outer radius equal to, the
native-norm mollifier scale. -/
noncomputable def parabolicMollifierBump (d n : ℕ) :
    ContDiffBump (0 : TimeVelocity d) :=
  ⟨parabolicMollifierScale n / 2, parabolicMollifierScale n,
    by
      unfold parabolicMollifierScale
      positivity,
    by
      apply half_lt_self
      unfold parabolicMollifierScale
      positivity⟩

/-- The normalized native-norm mollifier against the product volume. -/
noncomputable def parabolicMollifier (d n : ℕ) : TimeVelocity d → ℝ :=
  (parabolicMollifierBump d n).normed (volume : Measure (TimeVelocity d))

/-- The native-norm mollifier scales converge to zero. -/
theorem tendsto_parabolicMollifierScale_zero :
    Tendsto parabolicMollifierScale atTop (nhds 0) := by
  change Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0)
  exact
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))

variable (d n : ℕ)

/-- Each normalized native-norm mollifier is smooth. -/
theorem contDiff_parabolicMollifier :
    ContDiff ℝ ∞ (parabolicMollifier d n) := by
  exact (parabolicMollifierBump d n).contDiff_normed

/-- Each normalized native-norm mollifier has compact topological support. -/
theorem hasCompactSupport_parabolicMollifier :
    HasCompactSupport (parabolicMollifier d n) := by
  exact (parabolicMollifierBump d n).hasCompactSupport_normed

end HypoellipticAleksandrov.Parabolic
