module

public import GS.GlobalGeometry.SharedFactorCurves
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Certified descent with actual tied orthogonal factors

A generator lift of the exact shared projection is selected from its proved
existence.  Its matrix-exponential step preserves the actual physical block
ties for every real time when both block sizes are positive and divide the
matrix dimension.  The negative projected ambient gradient has loss slope
minus its squared Frobenius norm; Armijo steps and finite geometric
backtracking follow from differentiability at the base point.

The selected lift need not be unique.  No efficient solver, independence of
factor representation, shared-image manifold, or optimizer convergence rate
is asserted here.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.RiemannianCompletion Filter
open scoped Topology
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- A certified lift of the exact shared core projection. -/
def sharedProjectionGenerators (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Z : Mat n) :
    sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁ :=
  Classical.choose (frobProjection_mem (sharedCore b₁ b₂ τ₁ τ₂ P) (pull L (P * R) Z))

/-- Exponential step from the certified shared generator pair. -/
def sharedExpStep (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Z : Mat n) (t : ℝ) : Mat n :=
  gsExpCurve L P R (sharedProjectionGenerators b₁ b₂ τ₁ τ₂ P L R Z).1.val
    (sharedProjectionGenerators b₁ b₂ τ₁ τ₂ P L R Z).2.val t

@[simp] theorem sharedExpStep_zero (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Z : Mat n) :
    sharedExpStep b₁ b₂ τ₁ τ₂ P L R Z 0 = product2 L P R :=
  gsExpCurve_zero _ _ _ _ _

/-- The image of the actual tied orthogonal factors. -/
def InSharedA2Orth (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : Mat n) : Prop :=
  ∃ L R, SharedOrthogonalFactor b₂ τ₂ L ∧ SharedOrthogonalFactor b₁ τ₁ R ∧
    X = product2 L P R

/-- The negative ambient gradient is first exactly projected and then lifted
to a feasible exponential factor update. -/
def sharedDescentStep (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (f : Mat n → ℝ) : ℝ → Mat n :=
  sharedExpStep b₁ b₂ τ₁ τ₂ P L R (-ambientGradient f (product2 L P R))

@[simp] theorem sharedDescentStep_zero (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (P L R : Mat n) (f : Mat n → ℝ) :
    sharedDescentStep b₁ b₂ τ₁ τ₂ P L R f 0 = product2 L P R :=
  sharedExpStep_zero _ _ _ _ _ _ _ _

end GS.GlobalGeometry
