module

public import GS.Unitary.Support
public import Mathlib.Tactic.NoncommRing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.UnitaryGeometry
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

theorem skewHermitian_zero : IsSkewHermitian (0 : Matrix (Fin n) (Fin n) 𝕂) := by
  simp [IsSkewHermitian]

theorem skewHermitian_add {A B : Matrix (Fin n) (Fin n) 𝕂}
    (hA : IsSkewHermitian A) (hB : IsSkewHermitian B) :
    IsSkewHermitian (A + B) := by
  change Aᴴ = -A at hA; change Bᴴ = -B at hB
  simp only [IsSkewHermitian, Matrix.conjTranspose_add, hA, hB, neg_add]

theorem skewHermitian_real_smul (a : ℝ) {A : Matrix (Fin n) (Fin n) 𝕂}
    (hA : IsSkewHermitian A) : IsSkewHermitian (a • A) := by
  change Aᴴ = -A at hA
  simp only [IsSkewHermitian, Matrix.conjTranspose_smul, star_trivial, hA, smul_neg]

def kSupportedSkewSpace (𝕂 : Type*) [RCLike 𝕂] (block : Fin n → ℕ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) 𝕂) where
  carrier := {A | KSSupported block A ∧ IsSkewHermitian A}
  zero_mem' := ⟨KSSupported.zero, skewHermitian_zero⟩
  add_mem' hA hB := ⟨hA.1.add hB.1, skewHermitian_add hA.2 hB.2⟩
  smul_mem' a _ hA := ⟨KSSupported.real_smul a hA.1, skewHermitian_real_smul a hA.2⟩

abbrev supportedSkewSpace (block : Fin n → ℕ) := kSupportedSkewSpace ℂ block

theorem conjugate_skewHermitian (B C : Matrix (Fin n) (Fin n) 𝕂) (hC : IsSkewHermitian C) :
    IsSkewHermitian (B * C * Bᴴ) := by
  unfold IsSkewHermitian at *
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

def product2 {n : ℕ} (B₂ P B₁ : CMat n) : CMat n := B₂ * P * B₁

def kProduct2 {R : Type*} [Semiring R] {n : ℕ} (B₂ P B₁ : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R := B₂ * P * B₁

def tangentParam (B₂ P B₁ C Ω : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁

end GS.UnitaryGeometry
