module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.ComplexAlgebra
public import GS.Core
public import GS.Unitary.Support


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Real-linear generator algebra for complex unitary factors

All the generator spaces and maps in this module are over `ℝ`: the
skew-Hermitian condition is not preserved by arbitrary complex scaling.
The tangent spaces below are concrete generator images. These algebraic
statements do not assert an embedded manifold or quotient construction.
-/

noncomputable section
open Matrix
open scoped BigOperators

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
