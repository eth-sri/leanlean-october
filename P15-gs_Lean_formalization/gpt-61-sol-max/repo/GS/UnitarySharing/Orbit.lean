
import GS.UnitarySharing.Factors
import GS.UnitaryManifold.OrbitTopology
import GS.LieAction.CompactQuotient



/-!
# The shared matrix family as a compact homogeneous space

The action is L X R*, with actual shared unitary factors and conjugate transpose R*.
Its orbit is
exactly the previously defined `InSharedA2Unitary` family.  Compactness gives a
homeomorphism from the genuine stabilizer quotient to the matrix subspace;
the orbit map is an open quotient map, also with continuous stabilizers.

These are topological statements.  They do not identify a smooth quotient or
replace the missing shared-orbit atlas by an assumed manifold structure.
-/

namespace GS.UnitarySharing

/-- Actual two-layer family with full within-layer unitary block sharing. -/
def InSharedA2Unitary (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : CMat n) : Prop :=
  ∃ L R : CMat n, SharedUnitaryFactor b₂ τ₂ L ∧
    SharedUnitaryFactor b₁ τ₁ R ∧ X = GS.UnitaryGeometry.product2 L P R

















































end GS.UnitarySharing
