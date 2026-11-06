module

public import GS.Unitary.Support
public import Mathlib.Tactic.NoncommRing

@[expose] public section


/-!
# Real-linear generator algebra for complex unitary factors

All the generator spaces and maps in this module are over `ℝ`: the
skew-Hermitian condition is not preserved by arbitrary complex scaling.
The tangent spaces below are concrete generator images. These algebraic
statements do not assert an embedded manifold or quotient construction.
-/

noncomputable section
open Matrix

namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem skewHermitian_add {A B : CMat n}
    (hA : IsSkewHermitian A) (hB : IsSkewHermitian B) :
    IsSkewHermitian (A + B) := by
  change Aᴴ = -A at hA
  change Bᴴ = -B at hB
  simp only [IsSkewHermitian, Matrix.conjTranspose_add, hA, hB, neg_add]

theorem skewHermitian_real_smul (a : ℝ) {A : CMat n}
    (hA : IsSkewHermitian A) : IsSkewHermitian (a • A) := by
  change Aᴴ = -A at hA
  simp only [IsSkewHermitian, Matrix.conjTranspose_smul, star_trivial, hA, smul_neg]



/-- Block-supported skew-Hermitian generators, with real scalars. -/
def supportedSkewSpace (block : Fin n → ℕ) : Submodule ℝ (CMat n) where
  carrier := {A | CSupported block A ∧ IsSkewHermitian A}
  zero_mem' := ⟨CSupported.zero, by simp [IsSkewHermitian]⟩
  add_mem' := by
    rintro A B ⟨hsA,hkA⟩ ⟨hsB,hkB⟩
    exact ⟨hsA.add hsB, skewHermitian_add hkA hkB⟩
  smul_mem' := by
    rintro a A ⟨hsA,hkA⟩
    exact ⟨CSupported.real_smul a hsA, skewHermitian_real_smul a hkA⟩


theorem conjugate_skewHermitian (B C : CMat n) (hC : IsSkewHermitian C) :
    IsSkewHermitian (B*C*Bᴴ) := by
  unfold IsSkewHermitian at *
  simp_all
  grind



def product2 (B₂ P B₁ : CMat n) : CMat n := B₂ * P * B₁





end GS.UnitaryGeometry
