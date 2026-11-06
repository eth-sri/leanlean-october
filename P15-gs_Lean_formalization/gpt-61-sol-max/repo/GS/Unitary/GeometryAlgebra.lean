import GS.MatrixFactor.Factorization

import GS.Unitary.Support
import Mathlib.Tactic.NoncommRing



/-!
# Real-linear generator algebra for complex unitary factors

All the generator spaces and maps in this module are over `ℝ`: the
skew-Hermitian condition is not preserved by arbitrary complex scaling.
The tangent spaces below are concrete generator images. These algebraic
statements do not assert an embedded manifold or quotient construction.
-/


namespace GS.UnitaryGeometry


/-- Block-supported skew-Hermitian generators, with real scalars. -/
def supportedSkewSpace (block : Fin n → ℕ) : Submodule ℝ (CMat n) where
  carrier := {A | CSupported block A ∧ IsSkewHermitian A}
  zero_mem' := ⟨GS.MatrixBase.CSupported.zero, by ext <;> simp_all⟩
  add_mem' := by
    rintro A B ⟨hsA,hkA⟩ ⟨hsB,hkB⟩
    exact ⟨GS.MatrixBase.CSupported.add hsA hsB, (skewAdjoint _).add_mem hkA hkB⟩
  smul_mem' := by
    rintro a A ⟨hsA,hkA⟩
    exact ⟨GS.MatrixBase.CSupported.real_smul a hsA, skewAdjoint.smul_mem a hkA⟩



def product2 (B₂ P B₁ : CMat n) : CMat n := B₂ * P * B₁
end GS.UnitaryGeometry
