module

public import OAI.NumberTheory.PrimeGaps.DivisorBounds
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

def coordinateSum {j : ℕ} (t : Fin j → ℝ) : ℝ := ∑ i, t i

end LargePrimeGaps

end OAI
