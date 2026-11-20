module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing

/-!
# Reverse-time separated tests and dual pairings

This module constructs the canonical `L²(V)` class represented by a scalar
reverse-time test multiplied by a fixed spatial vector. It also packages the
continuous `L²(V*)`--`L²(V)` dual pairing and its integral representation.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The reverse-time interval carries a finite restricted volume measure. -/
theorem reverseTimeVolume_isFiniteMeasure (T : ℝ) :
    IsFiniteMeasure (reverseTimeVolume T) := by
  unfold reverseTimeVolume reverseTimeOpenInterval
  infer_instance

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ} (hΩ : IsOpen Ω) (q : ℝ → ℝ)

/-- Multiplication of a fixed spatial vector by a bounded time multiplier, as a CLM. -/
noncomputable def reverseTimeSeparatedVTestCLM (hq : MemLp q ∞ (reverseTimeVolume T)) :
    H10HilbertGraph hΩ →L[ℝ] ReverseTimeL2V hΩ T := by
  letI := reverseTimeVolume_isFiniteMeasure T
  exact ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ).holderL
    (reverseTimeVolume T) ∞ 2 2 (hq.toLp q)).comp (Lp.constL 2 (reverseTimeVolume T) ℝ)

/-- The reverse-time `L²(V)` class represented by `tau ↦ q tau • v`. -/
noncomputable def reverseTimeSeparatedVTestOfMemLp
    (hq : MeasureTheory.MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume T))
    (v : H10HilbertGraph hΩ) : ReverseTimeL2V hΩ T := 
  reverseTimeSeparatedVTestCLM hΩ q hq v

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ} (hΩ : IsOpen Ω)

/-- The separated multiplier has the literal scalar-multiple representative. -/
theorem ae_reverseTimeSeparatedVTestOfMemLp (q : ℝ → ℝ)
    (hq : MeasureTheory.MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume T))
    (v : H10HilbertGraph hΩ) :
    reverseTimeSeparatedVTestOfMemLp hΩ q hq v =ᵐ[reverseTimeVolume T]
      fun tau => q tau • v := by
  letI : IsFiniteMeasure (reverseTimeVolume T) :=
    reverseTimeVolume_isFiniteMeasure T
  rw [reverseTimeSeparatedVTestOfMemLp]
  change (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ).holder
    (2 : ℝ≥0∞) (hq.toLp q)
    ((MeasureTheory.Lp.constL (2 : ℝ≥0∞) (reverseTimeVolume T) ℝ) v) =ᵐ[_] _
  filter_upwards [ContinuousLinearMap.coeFn_holder
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
        H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
      (r := (2 : ℝ≥0∞))
      (hq.toLp q)
    ((MeasureTheory.Lp.constL (2 : ℝ≥0∞) (reverseTimeVolume T) ℝ) v),
    hq.coeFn_toLp,
    MeasureTheory.Lp.coeFn_const (p := (2 : ℝ≥0∞))
      (μ := reverseTimeVolume T) v] with tau hmul hq' hconst
  rw [MeasureTheory.Lp.constL_apply] at hmul ⊢
  rw [hmul, hq', hconst]
  rfl

/-- The reverse-time `L²(V)` class represented by `τ ↦ eta τ • v`. -/
noncomputable def reverseTimeSeparatedVTest (eta : ReverseTimeScalarTest T) (v : H10HilbertGraph hΩ) :
    ReverseTimeL2V hΩ T := 
  reverseTimeSeparatedVTestOfMemLp hΩ eta (eta.memLp ∞) v

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

section
variable (hΩ : IsOpen Ω) (T : ℝ)

/-- The continuous `L²(V*)`--`L²(V)` pairing over the reverse-time volume. -/
noncomputable def reverseTimeDualPairingCLM :
    ReverseTimeL2VStar hΩ T →L[ℝ] ReverseTimeL2V hΩ T →L[ℝ] ℝ :=
  let pairing : H10HilbertGraphDual hΩ →L[ℝ]
      H10HilbertGraph hΩ →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)
  pairing.lpPairing (reverseTimeVolume T) (2 : ℝ≥0∞) (2 : ℝ≥0∞)

/-- The reverse-time dual pairing is the integral of the literal pointwise pairing. -/
theorem reverseTimeDualPairingCLM_apply
    (g : ReverseTimeL2VStar hΩ T) (z : ReverseTimeL2V hΩ T) :
    reverseTimeDualPairingCLM hΩ T g z =
      ∫ tau, g tau (z tau) ∂reverseTimeVolume T := by
  unfold reverseTimeDualPairingCLM
  dsimp only
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply]

end

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
