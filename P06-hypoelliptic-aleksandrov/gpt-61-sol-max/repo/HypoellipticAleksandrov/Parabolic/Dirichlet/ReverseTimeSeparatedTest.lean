module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov

open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeVolume_isFiniteMeasure from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov


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
alias reverseTimeVolume_isFiniteMeasure := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeVolume_isFiniteMeasure


variable {d : ℕ} {Ω : PDE.VelocityRegion d}

variable {T : ℝ} (hΩ : IsOpen Ω) (eta : ReverseTimeScalarTest T)

variable (v : H10HilbertGraph hΩ)

/-- The reverse-time `L²(V)` class represented by `τ ↦ eta τ • v`. -/
def reverseTimeSeparatedVTest
       :
    ReverseTimeL2V hΩ T := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  exact
    (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
      H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)).holderL
      (reverseTimeVolume T) (∞ ) (2 ) (2 )
      ((eta.memLp ∞).toLp eta))
      ((MeasureTheory.Lp.constL (2 ) (reverseTimeVolume T) ℝ) v)

/-- The separated reverse-time test has the literal scalar-multiple representative. -/
theorem ae_reverseTimeSeparatedVTest
       :
    reverseTimeSeparatedVTest hΩ eta v =ᵐ[reverseTimeVolume T]
      fun tau => eta tau • v := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  rw [reverseTimeSeparatedVTest]
  change (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ).holder
    (2 ) ((eta.memLp ∞).toLp eta)
    ((MeasureTheory.Lp.constL (2 ) (reverseTimeVolume T) ℝ) v) =ᵐ[_] _
  filter_upwards [ContinuousLinearMap.coeFn_holder
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
        H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
      (r := (2 ))
      ((eta.memLp ∞).toLp eta)
    ((MeasureTheory.Lp.constL (2 ) (reverseTimeVolume T) ℝ) v),
    (eta.memLp ∞).coeFn_toLp,
    MeasureTheory.Lp.coeFn_const (p := (2 ))
      (μ := reverseTimeVolume T) v] with tau hmul heta hconst
  rw [MeasureTheory.Lp.constL_apply] at hmul ⊢
  rw [hmul, heta, hconst]
  rfl

/-- Separated reverse-time tests depend continuously on their spatial vector. -/
theorem tendsto_reverseTimeSeparatedVTest

    {vN : ℕ → H10HilbertGraph hΩ} {v : H10HilbertGraph hΩ}
    (hv : Tendsto vN atTop (𝓝 v)) :
    Tendsto (fun n => reverseTimeSeparatedVTest hΩ eta (vN n)) atTop
      (𝓝 (reverseTimeSeparatedVTest hΩ eta v)) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  let L : H10HilbertGraph hΩ →L[ℝ] ReverseTimeL2V hΩ T :=
    ((((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
      H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)).holderL
      (reverseTimeVolume T) (∞ ) (2 ) (2 )
      ((eta.memLp ∞).toLp eta)).comp
      (MeasureTheory.Lp.constL (2 ) (reverseTimeVolume T) ℝ))
  change Tendsto (fun n => L (vN n)) atTop (𝓝 (L v))
  exact L.continuous.tendsto v |>.comp hv

variable (hΩ : IsOpen Ω) (T : ℝ)

/-- The continuous `L²(V*)`--`L²(V)` pairing over the reverse-time volume. -/
def reverseTimeDualPairingCLM

     :
    ReverseTimeL2VStar hΩ T →L[ℝ] ReverseTimeL2V hΩ T →L[ℝ] ℝ :=
  let pairing : H10HilbertGraphDual hΩ →L[ℝ]
      H10HilbertGraph hΩ →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)
  pairing.lpPairing (reverseTimeVolume T) (2 ) (2 )

/-- The reverse-time dual pairing is the integral of the literal pointwise pairing. -/
theorem reverseTimeDualPairingCLM_apply


    (g : ReverseTimeL2VStar hΩ T) (z : ReverseTimeL2V hΩ T) :
    reverseTimeDualPairingCLM hΩ T g z =
      ∫ tau, g tau (z tau) ∂reverseTimeVolume T := by
  unfold reverseTimeDualPairingCLM
  dsimp only
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply]

end HypoellipticAleksandrov.Parabolic.Dirichlet
