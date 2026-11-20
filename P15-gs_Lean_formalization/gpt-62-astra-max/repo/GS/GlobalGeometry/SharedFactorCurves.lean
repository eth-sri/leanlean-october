module

public import GS.GlobalGeometry.SharedAlgebra
public import GS.GlobalGeometry.SharedNormalEquations
public import GS.Continuation.FactorCurveVelocities

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Actual curves and feasible exponential updates with tied blocks

For full physical blocks (`0 < b` and `b ∣ n`), equal local block entries
are preserved by products, transposes and the matrix exponential.  Consequently
all shared generator directions are realized by differentiable curves of
actual tied orthogonal factors, and every differentiable factor curve has one
of these directions.

This identifies velocities of differentiable factor curves, rather than
assuming that every curve in the image admits a differentiable factor lift.
No smooth manifold assertion for an arbitrary shared image is made here.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- An actual finite matrix factor with the specified physical block ties. -/
def SharedOrthogonalFactor (b : ℕ) (τ : ℕ → ℕ) (A : Mat n) : Prop :=
  BlockDiagonal b A ∧ Orthogonal A ∧ TiedEntries b τ A

/-- A finite exponential step preserves orthogonality, block support and
all ties, for every real step size. -/
theorem gsExpLeft_shared (b : ℕ) (τ : ℕ → ℕ) (hb : 0 < b) (hbn : b ∣ n)
    (B C : Mat n) (hB : SharedOrthogonalFactor b τ B)
    (hC : C ∈ sharedSkewSpace b τ) (t : ℝ) :
    SharedOrthogonalFactor b τ (gsExpLeft B C t) := by
  refine ⟨gsExpLeft_supported B C hB.1 hC.1 t,
    gsExpLeft_orthogonal B C hB.2.1 hC.2.1 t, ?_⟩
  exact TiedEntries.mul hb hbn hB.1 (expLine_supported hC.1 t)
    hB.2.2 (expLine_tied hb hbn hC.1 hC.2.2 t)

theorem gsExpRight_shared (b : ℕ) (τ : ℕ → ℕ) (hb : 0 < b) (hbn : b ∣ n)
    (B Ω : Mat n) (hB : SharedOrthogonalFactor b τ B)
    (hΩ : Ω ∈ sharedSkewSpace b τ) (t : ℝ) :
    SharedOrthogonalFactor b τ (gsExpRight B Ω t) := by
  refine ⟨gsExpRight_supported B Ω hB.1 hΩ.1 t,
    gsExpRight_orthogonal B Ω hB.2.1 hΩ.2.1 t, ?_⟩
  exact TiedEntries.mul hb hbn (expLine_supported hΩ.1 t) hB.1
    (expLine_tied hb hbn hΩ.1 hΩ.2.2 t) hB.2.2

end GS.GlobalGeometry
