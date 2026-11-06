module

public import GS.Unitary.Support
public import Mathlib.Tactic.NoncommRing

@[expose] public section

noncomputable section
open Matrix

namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem skewHermitian_zero : IsSkewHermitian (0 : CMat n) := by
  simp [IsSkewHermitian]

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
  zero_mem' := ⟨CSupported.zero, skewHermitian_zero⟩
  add_mem' := by
    rintro A B ⟨hsA,hkA⟩ ⟨hsB,hkB⟩
    exact ⟨hsA.add hsB, skewHermitian_add hkA hkB⟩
  smul_mem' := by
    rintro a A ⟨hsA,hkA⟩
    exact ⟨CSupported.real_smul a hsA, skewHermitian_real_smul a hkA⟩

theorem conjugate_skewHermitian (B C : CMat n) (hC : IsSkewHermitian C) :
    IsSkewHermitian (B*C*Bᴴ) := by
  unfold IsSkewHermitian at *
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

def product2 (B₂ P B₁ : CMat n) : CMat n := B₂ * P * B₁

def tangentParam (B₂ P B₁ C Ω : CMat n) : CMat n :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁

end GS.UnitaryGeometry
