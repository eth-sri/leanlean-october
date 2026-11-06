module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GelfandTriple
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Reverse-time Bochner spaces

This module defines the quotient-valued Bochner `L²` carriers over the literal
reverse-time interval and lifts the spatial Gelfand-triple maps to them.
It makes only almost-everywhere representative statements, never fixed-time
evaluation or temporal regularity claims.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The open reverse-time interval, including the empty case `T ≤ 0`. -/
def reverseTimeOpenInterval (T : ℝ) : Set ℝ :=
  Set.Ioo 0 T

/-- Lebesgue measure restricted to the literal open reverse-time interval. -/
def reverseTimeVolume (T : ℝ) : Measure ℝ :=
  volume.restrict (reverseTimeOpenInterval T)

/-- Bochner `L²` curves with values in the zero-boundary spatial Hilbert graph. -/
abbrev ReverseTimeL2V
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) : Type _ :=
  MeasureTheory.Lp (H10HilbertGraph hΩ) (2 ) (reverseTimeVolume T)

/-- Bochner `L²` curves with values in spatial restricted-volume `L²`. -/
abbrev ReverseTimeL2H
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) : Type _ :=
  MeasureTheory.Lp (PDE.ScalarLp Ω (2 )) (2 )
    (reverseTimeVolume T)

/-- Bochner `L²` curves with values in the spatial Gelfand dual. -/
abbrev ReverseTimeL2VStar
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) : Type _ :=
  MeasureTheory.Lp (H10HilbertGraphDual hΩ) (2 )
    (reverseTimeVolume T)

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ)

/-- Pointwise application of the spatial value map, lifted to Bochner `L²`. -/
def reverseTimeValueCLM
     :
    ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2H hΩ T :=
  (valueCLM hΩ).compLpL (2 ) (reverseTimeVolume T)

/-- Pointwise application of the spatial pivot map, lifted to Bochner `L²`. -/
def reverseTimePivotCLM
     :
    ReverseTimeL2H hΩ T →L[ℝ] ReverseTimeL2VStar hΩ T :=
  (scalarLpToH10HilbertGraphDual hΩ).compLpL (2 )
    (reverseTimeVolume T)

/-- The timewise Gelfand embedding `V → H → V*`. -/
def reverseTimeGelfandCLM
     :
    ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2VStar hΩ T :=
  (reverseTimePivotCLM hΩ T).comp (reverseTimeValueCLM hΩ T)

/-- Almost-everywhere formula for the Bochner lift of the spatial value map. -/
theorem coeFn_reverseTimeValueCLM

    (u : ReverseTimeL2V hΩ T) :
    reverseTimeValueCLM hΩ T u =ᵐ[reverseTimeVolume T]
      fun τ => valueCLM hΩ (u τ) :=
  ContinuousLinearMap.coeFn_compLpL (valueCLM hΩ) u

/-- Almost-everywhere formula for the Bochner lift of the spatial pivot map. -/
theorem coeFn_reverseTimePivotCLM

    (h : ReverseTimeL2H hΩ T) :
    reverseTimePivotCLM hΩ T h =ᵐ[reverseTimeVolume T]
      fun τ => scalarLpToH10HilbertGraphDual hΩ (h τ) :=
  ContinuousLinearMap.coeFn_compLpL (scalarLpToH10HilbertGraphDual hΩ) h

/-- Almost-everywhere formula for the composed timewise Gelfand map. -/
theorem coeFn_reverseTimeGelfandCLM

    (u : ReverseTimeL2V hΩ T) :
    reverseTimeGelfandCLM hΩ T u =ᵐ[reverseTimeVolume T]
      fun τ => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (u τ)) := by
  filter_upwards [coeFn_reverseTimePivotCLM hΩ T
      (reverseTimeValueCLM hΩ T u), coeFn_reverseTimeValueCLM hΩ T u]
    with τ hPivot hValue
  change ((reverseTimePivotCLM hΩ T) (reverseTimeValueCLM hΩ T u)) τ = _
  rw [hPivot, hValue]

end HypoellipticAleksandrov.Parabolic.Dirichlet
