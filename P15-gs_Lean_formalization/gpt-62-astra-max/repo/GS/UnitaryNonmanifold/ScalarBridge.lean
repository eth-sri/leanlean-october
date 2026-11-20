module

public import GS.OriginalLocalModel
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact scalar perfect-shuffle description of the unitary block family

This file identifies the block description with the original three-factor
family using its prescribed scalar shuffle, including degenerate entries.
-/
noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryNonmanifold
open GS.UnitaryGeometry

def localFamily (q : ℕ) : Set (CMat (q*2)) :=
  let P := cPermMatrix (scalarShuffle q 2)
  {M | CInA3Unitary 2 q 2 P Pᴴ M}

end GS.UnitaryNonmanifold
