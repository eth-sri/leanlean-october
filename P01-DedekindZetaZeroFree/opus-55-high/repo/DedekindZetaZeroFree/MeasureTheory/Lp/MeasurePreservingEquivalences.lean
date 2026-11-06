module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/MeasureTheory/Function/Lp/CompMeasurePreservingEquiv.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

namespace Lp

@[simp]
theorem compMeasurePreservingₗᵢ_apply {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E] {f : α → β}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (x : Lp E p μb) :
    compMeasurePreservingₗᵢ 𝕜 f hf x = compMeasurePreserving f hf x :=
  rfl
