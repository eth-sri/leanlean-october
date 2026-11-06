module

public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.W1p.Mean

/-!
# Integral means for representative-level `H¹`

This file is the LIH-compatible `p = 2` facade over the generic
`W1pFunction` mean API. Constants, addition of constants, subtraction of the
average, and the zero-mean theorem are transported without repeating the
underlying integrability or weak-derivative arguments.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The constant `H¹(U)` representative with zero weak gradient. -/
noncomputable def const [IsFiniteMeasure (volumeOn U)]
    (c : ℝ) : H1Function U :=
  (W1pFunction.const (U := U) (p := (2 )) c).toH1Function





/-- Add a scalar constant without changing the chosen weak gradient. -/
noncomputable def addConst [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U) (c : ℝ) : H1Function U :=
  (u.toW1pFunction.addConst c).toH1Function

@[simp]
theorem addConst_apply [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U) (c : ℝ) (x : Vec d) :
    u.addConst c x = u x + c :=
  rfl












end H1Function

end PDE
