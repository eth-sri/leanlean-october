module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Logarithmic scales and normalized (one-bounded) weights. -/

@[expose] public section

namespace Erdos408

/-- `T = log log x`. -/
noncomputable abbrev logLog (x : ℝ) : ℝ :=
  Real.log (Real.log x)

/-- `s = log log log x`. -/
noncomputable abbrev logLogLog (x : ℝ) : ℝ :=
  Real.log (logLog x)

/-- Pointwise unit-ball bound for a weight. -/
abbrev OneBounded {ι E : Type*} [SeminormedAddGroup E] (f : ι → E) : Prop :=
  ∀ i, ‖f i‖ ≤ 1

end Erdos408
