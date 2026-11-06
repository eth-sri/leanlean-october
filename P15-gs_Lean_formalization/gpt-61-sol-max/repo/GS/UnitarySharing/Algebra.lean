
import GS.GlobalGeometry.SharedAlgebra
import GS.UnitaryManifold.CayleySmooth
import GS.UnitaryManifold.BlockGroup
import GS.Unitary.FrobeniusProjection



/-!
# Complex complete-block sharing as a real star algebra

The equality predicate is imposed on actual complex entries. Positive complete
physical blocks have the same finite local index set, so products preserve all
within-layer ties. Inverse closure is derived by finite-dimensional real linear
algebra. Neither skew-Hermitian generators nor the Cayley chart discard phases.
-/
open GS.UnitaryGeometry
namespace GS.UnitarySharing
variable  {τ : ℕ → ℕ} {A : CMat n}

variable (b : ℕ)

/-- Labels tie full complex blocks within one layer, never across layers. -/
def TiedEntries  (τ : ℕ → ℕ) (A : CMat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'















def SharedUnitaryFactor  (τ : ℕ → ℕ) (A : CMat n) : Prop :=
  CSupported (fun i => i.val / b) A ∧ Unitary A ∧ TiedEntries b τ A

















end GS.UnitarySharing
