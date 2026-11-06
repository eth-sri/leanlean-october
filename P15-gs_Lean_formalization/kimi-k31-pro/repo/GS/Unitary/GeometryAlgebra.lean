module

public import GS.Unitary.Support
public import Mathlib.Tactic.NoncommRing

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

/-- The Lie algebra of unitary matrices is a real vector space. -/
def skewHermitianSpace : Submodule ℝ (CMat n) where
  carrier := {A | IsSkewHermitian A}
  zero_mem' := skewHermitian_zero
  add_mem' := skewHermitian_add
  smul_mem' := skewHermitian_real_smul

@[simp] theorem mem_skewHermitianSpace (A : CMat n) :
    A ∈ skewHermitianSpace ↔ IsSkewHermitian A := Iff.rfl

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

@[simp] theorem mem_supportedSkewSpace (block : Fin n → ℕ) (A : CMat n) :
    A ∈ supportedSkewSpace block ↔ CSupported block A ∧ IsSkewHermitian A := Iff.rfl

theorem conjugate_skewHermitian (B C : CMat n) (hC : IsSkewHermitian C) :
    IsSkewHermitian (B*C*Bᴴ) := by
  unfold IsSkewHermitian at *
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem conjugate_supported (block : Fin n → ℕ) (B C : CMat n)
    (hB : CSupported block B) (hC : CSupported block C) :
    CSupported block (B*C*Bᴴ) := (hB.mul hC).mul hB.conjTranspose

theorem conjugate_mem_supportedSkewSpace (block : Fin n → ℕ) (B C : CMat n)
    (hB : CSupported block B) (hC : C ∈ supportedSkewSpace block) :
    B*C*Bᴴ ∈ supportedSkewSpace block :=
  ⟨conjugate_supported block B C hB hC.1, conjugate_skewHermitian B C hC.2⟩

def product2 (B₂ P B₁ : CMat n) : CMat n := B₂ * P * B₁

def tangentParam (B₂ P B₁ C Ω : CMat n) : CMat n :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁

/-- Concrete differential of the factor parametrization on real generator spaces. -/
def tangentParamMap (block₁ block₂ : Fin n → ℕ) (B₂ P B₁ : CMat n) :
    (supportedSkewSpace block₂ × supportedSkewSpace block₁) →ₗ[ℝ] CMat n where
  toFun v := tangentParam B₂ P B₁ v.1.val v.2.val
  map_add' v w := by
    simp only [tangentParam, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' a v := by
    change tangentParam B₂ P B₁ (a • v.1.val) (a • v.2.val) =
      a • tangentParam B₂ P B₁ v.1.val v.2.val
    simp only [tangentParam, Matrix.mul_smul, Matrix.smul_mul, smul_add]

def tangentParamSpace (block₁ block₂ : Fin n → ℕ) (B₂ P B₁ : CMat n) :
    Submodule ℝ (CMat n) := LinearMap.range (tangentParamMap block₁ block₂ B₂ P B₁)

theorem mem_tangentParamSpace_iff (block₁ block₂ : Fin n → ℕ) (B₂ P B₁ Y : CMat n) :
    Y ∈ tangentParamSpace block₁ block₂ B₂ P B₁ ↔
      ∃ C ∈ supportedSkewSpace block₂, ∃ Ω ∈ supportedSkewSpace block₁,
        tangentParam B₂ P B₁ C Ω = Y := by
  constructor
  · rintro ⟨⟨C,Ω⟩,he⟩
    exact ⟨C,C.property,Ω,Ω.property,he⟩
  · rintro ⟨C,hC,Ω,hΩ,he⟩
    exact ⟨(⟨C,hC⟩,⟨Ω,hΩ⟩),he⟩

end GS.UnitaryGeometry
