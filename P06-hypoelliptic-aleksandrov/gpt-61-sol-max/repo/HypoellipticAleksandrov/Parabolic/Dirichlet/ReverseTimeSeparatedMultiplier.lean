module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedTest
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov

open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeVolume_isFiniteMeasure from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov


/-!
# Reverse-time separated bounded-scalar multipliers

This module extends separated reverse-time tests from smooth scalar tests to
arbitrary essentially bounded scalar multipliers.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The reverse-time interval has finite volume. -/
alias reverseTimeVolume_isFiniteMeasure_ofMemLp := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeVolume_isFiniteMeasure


variable {d : ℕ} {Ω : PDE.VelocityRegion d} {T : ℝ} (hΩ : IsOpen Ω) (q : ℝ → ℝ) (hq : MeasureTheory.MemLp q (∞ ) (reverseTimeVolume T))

variable (v : H10HilbertGraph hΩ)

/-- The reverse-time `L²(V)` class represented by `tau ↦ q tau • v`. -/
def reverseTimeSeparatedVTestOfMemLp

     : ReverseTimeL2V hΩ T := by
  letI : IsFiniteMeasure (reverseTimeVolume T) :=
    reverseTimeVolume_isFiniteMeasure_ofMemLp T
  exact
    (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
      H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)).holderL
      (reverseTimeVolume T) (∞ ) (2 ) (2 )
      (hq.toLp q))
      ((MeasureTheory.Lp.constL (2 ) (reverseTimeVolume T) ℝ) v)

/-- The separated multiplier has the literal scalar-multiple representative. -/
theorem ae_reverseTimeSeparatedVTestOfMemLp

     :
    reverseTimeSeparatedVTestOfMemLp hΩ q hq v =ᵐ[reverseTimeVolume T]
      fun tau => q tau • v := by
  letI : IsFiniteMeasure (reverseTimeVolume T) :=
    reverseTimeVolume_isFiniteMeasure_ofMemLp T
  rw [reverseTimeSeparatedVTestOfMemLp]
  change (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ).holder
    (2 ) (hq.toLp q)
    ((MeasureTheory.Lp.constL (2 ) (reverseTimeVolume T) ℝ) v) =ᵐ[_] _
  filter_upwards [ContinuousLinearMap.coeFn_holder
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
        H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
      (r := (2 ))
      (hq.toLp q)
    ((MeasureTheory.Lp.constL (2 ) (reverseTimeVolume T) ℝ) v),
    hq.coeFn_toLp,
    MeasureTheory.Lp.coeFn_const (p := (2 ))
      (μ := reverseTimeVolume T) v] with tau hmul hq' hconst
  rw [MeasureTheory.Lp.constL_apply] at hmul ⊢
  rw [hmul, hq', hconst]
  rfl

/-- Separated reverse-time multipliers depend continuously on their spatial vector. -/
theorem tendsto_reverseTimeSeparatedVTestOfMemLp

    {vN : ℕ → H10HilbertGraph hΩ} {v : H10HilbertGraph hΩ}
    (hv : Filter.Tendsto vN Filter.atTop (𝓝 v)) :
    Filter.Tendsto
      (fun n => reverseTimeSeparatedVTestOfMemLp hΩ q hq (vN n))
      Filter.atTop (𝓝 (reverseTimeSeparatedVTestOfMemLp hΩ q hq v)) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) :=
    reverseTimeVolume_isFiniteMeasure_ofMemLp T
  let L : H10HilbertGraph hΩ →L[ℝ] ReverseTimeL2V hΩ T :=
    ((((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
      H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)).holderL
      (reverseTimeVolume T) (∞ ) (2 ) (2 )
      (hq.toLp q)).comp
      (MeasureTheory.Lp.constL (2 ) (reverseTimeVolume T) ℝ))
  change Filter.Tendsto (fun n => L (vN n)) Filter.atTop (𝓝 (L v))
  exact L.continuous.tendsto v |>.comp hv

end HypoellipticAleksandrov.Parabolic.Dirichlet
