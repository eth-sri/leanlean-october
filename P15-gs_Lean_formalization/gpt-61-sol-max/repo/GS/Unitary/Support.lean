import GS.MatrixGeometry.Base

import GS.ComplexAlgebra
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.NoncommRing



/-! Complex support algebra uses conjugate transpose throughout. -/
namespace GS.UnitaryGeometry

/-- A complex matrix with entries only within equal block labels. -/
def CSupported (block : Fin n → ℕ) (A : CMat n) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0




















end GS.UnitaryGeometry
