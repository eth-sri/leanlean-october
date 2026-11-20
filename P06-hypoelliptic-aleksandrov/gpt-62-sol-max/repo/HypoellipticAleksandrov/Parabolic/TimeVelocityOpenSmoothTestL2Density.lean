module

import HypoellipticAleksandrov.Analysis.InteriorSmoothDensity

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives

/-!
# Interior-supported smooth functions are dense in time--velocity `L²`

On every open subset of time--velocity space, globally smooth compactly supported
real functions whose topological support remains in that subset are dense for the
restricted-volume `L²` norm.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

/-- Globally smooth compactly supported functions whose topological support lies
in an open time--velocity carrier are dense in its restricted real `L²`. -/
theorem dense_smoothCompactlySupported_toLp_timeVelocity
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U) :
    Dense {q : Lp ℝ (2 : ℝ≥0∞) (timeVelocityVolumeOn U) |
      ∃ (φ : TimeVelocity d → ℝ)
          (hφ : ParabolicMemLpOn U (2 : ℝ≥0∞) φ),
        ContDiff ℝ (⊤ : ℕ∞) φ ∧
        HasCompactSupport φ ∧
        tsupport φ ⊆ U ∧
        q = hφ.toLp φ} := Analysis.dense_interior_smooth_toLp volume hU

end HypoellipticAleksandrov.Parabolic
