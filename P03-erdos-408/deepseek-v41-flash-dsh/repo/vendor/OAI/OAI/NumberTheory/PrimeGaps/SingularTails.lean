module

public import OAI.NumberTheory.PrimeGaps.SingularSeries
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

def boxTuple {s h : ℕ} (a : Fin s → ℤ) (n : Fin s → Fin h) : Fin s → ℤ :=
  fun i => a i + (n i:ℕ)

end LargePrimeGaps

end OAI
