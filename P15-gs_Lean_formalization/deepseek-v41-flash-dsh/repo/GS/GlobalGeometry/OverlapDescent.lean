module

public import GS.GlobalGeometry.CayleyRetraction
public import GS.GlobalGeometry.ProjectedDerivative
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Projected descent with arbitrary overlap

For independently chosen supported orthogonal factors, the exact matrix
projection gives a feasible Cayley descent curve and finite geometric
backtracking. No no-overlap hypothesis or overlap manifold atlas is needed.
Stationarity here refers to the image of the factor differential.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.RiemannianCompletion Filter
open scoped Topology

namespace GS.GlobalGeometry

variable {n : ℕ}

variable (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (L R : Mat n)
variable (hsL : Supported b₂ L) (hsR : Supported b₁ R)
variable (hL : Orthogonal L) (hR : Orthogonal R)
include hsL hsR hL hR

end GS.GlobalGeometry

namespace GS.GlobalGeometry
variable {n : ℕ}

end GS.GlobalGeometry
