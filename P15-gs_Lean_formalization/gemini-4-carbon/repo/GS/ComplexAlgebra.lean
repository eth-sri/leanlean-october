module

public import GS.Core
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix
namespace GS

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def Unitary {n : ℕ} (A : CMat n) : Prop := Aᴴ*A=1 ∧ A*Aᴴ=1

def KUnitary {𝕂 : Type*} [RCLike 𝕂] {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕂) : Prop :=
  Aᴴ * A = 1 ∧ A * Aᴴ = 1

@[simp] theorem kUnitary_complex_iff {n : ℕ} (A : CMat n) : KUnitary A ↔ Unitary A := by
  simp [KUnitary, Unitary]

def IsSkewHermitian {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕂) : Prop := Aᴴ = -A

def skewHermitianPart {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  (1 / 2 : ℝ) • (A - Aᴴ)

namespace KUnitary
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ} {A B : Matrix (Fin n) (Fin n) 𝕂}

theorem one : KUnitary (1 : Matrix (Fin n) (Fin n) 𝕂) := ⟨by simp, by simp⟩
theorem conjTranspose (h : KUnitary A) : KUnitary Aᴴ := ⟨by simpa using h.2, by simpa using h.1⟩
theorem mul (hA : KUnitary A) (hB : KUnitary B) : KUnitary (A * B) :=
  ⟨by calc (A * B)ᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hA.1]; simpa using hB.1,
   by calc (A * B) * (A * B)ᴴ = A * (B * Bᴴ) * Aᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hB.2]; simpa using hA.2⟩
end KUnitary

namespace Unitary
variable {n : ℕ} {A B : CMat n}
theorem one : Unitary (1 : CMat n) := ⟨by simp, by simp⟩
theorem conjTranspose (h : Unitary A) : Unitary Aᴴ := ⟨by simpa using h.2, by simpa using h.1⟩
theorem mul (hA : Unitary A) (hB : Unitary B) : Unitary (A * B) :=
  ⟨by calc (A * B)ᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hA.1]; simpa using hB.1,
   by calc (A * B) * (A * B)ᴴ = A * (B * Bᴴ)*Aᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hB.2]; simpa using hA.2⟩
end Unitary
end GS
