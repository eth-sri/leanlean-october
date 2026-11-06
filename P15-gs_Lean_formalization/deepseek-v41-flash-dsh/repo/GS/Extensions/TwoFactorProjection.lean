module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.Core
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.Projection


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Connect the supported-skew projector to the two-factor differential image

No sharing is imposed in this module.
Both overlapping and nonoverlapping supports are treated exactly. The range is
the image of an actual Frechet derivative on specified generator directions;
this module does not yet identify it with an embedded manifold tangent space.
-/

noncomputable section
open Matrix
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

 def TwoFactorDirection (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ X : Mat n) : Prop :=
  ∃ C Ω : Mat n, Supported block₂ C ∧ IsSkew C ∧
    Supported block₁ Ω ∧ IsSkew Ω ∧ X = tangentParam B₂ P B₁ C Ω

 theorem isSkew_add {C K : Mat n} (hC : IsSkew C) (hK : IsSkew K) :
    IsSkew (C+K) := by
  unfold IsSkew at *
  rw [Matrix.transpose_add, hC, hK]
  abel

end GS.Extensions
