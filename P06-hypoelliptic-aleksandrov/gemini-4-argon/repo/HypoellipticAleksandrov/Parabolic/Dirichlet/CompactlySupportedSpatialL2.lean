module

public import PDEFoundation.Measure.LpSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Compactly supported continuous functions in restricted scalar `L²`

This module packages a continuous compactly supported scalar function into the
canonical restricted scalar `L²` carrier on an arbitrary raw spatial set.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory
open scoped ENNReal

/- Package a continuous compactly supported scalar function in restricted
scalar `L²` on an arbitrary raw spatial carrier. -/
noncomputable def compactlySupportedContinuousToScalarLp
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ) (hq : Continuous q) (hqcompact : HasCompactSupport q) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  ((hq.memLp_of_hasCompactSupport hqcompact).restrict Ω).toLp q

/- The canonical restricted scalar `L²` package agrees almost everywhere with
its supplied continuous compactly supported function. -/
theorem coeFn_compactlySupportedContinuousToScalarLp
    {d Ω}
    (q : PDE.Vec d → ℝ) (hq : Continuous q) (hqcompact : HasCompactSupport q) :
    ⇑(compactlySupportedContinuousToScalarLp (Ω := Ω) q hq hqcompact) =ᵐ[PDE.volumeOn Ω] q :=  ((hq.memLp_of_hasCompactSupport hqcompact).restrict Ω).coeFn_toLp

/- A uniformly bounded continuous field supported in a compact carrier has
the corresponding restricted-volume squared-energy bound. -/
end HypoellipticAleksandrov.Parabolic.Dirichlet
