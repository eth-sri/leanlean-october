module

public import GS.UnitaryNonmanifold.BlockInvariant
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# First-order restrictions from commuting Hermitian block Grams

At a scalar base point, pairwise commutation of two matrix curves imposes a
quadratic restriction on their derivatives. This is a restriction on actual
curve velocities, including curves that do not lift differentiably to factors.
-/

noncomputable section
open Matrix Filter
open scoped Topology
namespace GS.UnitaryNonmanifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

end GS.UnitaryNonmanifold
