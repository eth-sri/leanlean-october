module

public import GS.Unitary.PointProjection
public import GS.Unitary.ProjectionRegularity
public import GS.Unitary.Permutations
public import GS.UnitaryManifold.Action

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Canonical supported skew-Hermitian generators depending only on the
base matrix and ambient vector. Arbitrary overlap of independent blocks is allowed. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable
open Matrix GS GS.UnitaryManifold
namespace GS.UnitaryGeometry
variable {n : ℕ}

def blockSkew (block : Fin n → ℕ) (A : CMat n) : CMat n :=
  maskedSkewHermitian (fun i j => block i = block j) A

def leftPointProjection (block : Fin n → ℕ) (X Z : CMat n) : CMat n :=
  blockSkew block (Z * Xᴴ) * X

def rightPointProjection (block : Fin n → ℕ) (X Z : CMat n) : CMat n :=
  X * blockSkew block (Xᴴ * Z)

@[simp] theorem blockSkew_add (b : Fin n → ℕ) (A B : CMat n) :
    blockSkew b (A+B) = blockSkew b A + blockSkew b B :=
  (maskedSkewHermitianMap (fun i j => b i = b j)).map_add A B

@[simp] theorem blockSkew_smul (b : Fin n → ℕ) (a : ℝ) (A : CMat n) :
    blockSkew b (a • A) = a • blockSkew b A :=
  (maskedSkewHermitianMap (fun i j => b i = b j)).map_smul a A

@[simp] theorem blockSkew_zero (b : Fin n → ℕ) : blockSkew b (0 : CMat n) = 0 :=
  (maskedSkewHermitianMap (fun i j => b i = b j)).map_zero

theorem blockSkew_sub (b : Fin n → ℕ) (A B : CMat n) :
    blockSkew b (A-B) = blockSkew b A - blockSkew b B :=
  (maskedSkewHermitianMap (fun i j => b i = b j)).map_sub A B

theorem blockSkew_supported (b : Fin n → ℕ) (A : CMat n) :
    CSupported b (blockSkew b A) := maskedSkewHermitian_hasSupport _ _

theorem blockSkew_skew (b : Fin n → ℕ) (A : CMat n) :
    IsSkewHermitian (blockSkew b A) := maskedSkewHermitian_isSkewHermitian (fun _ _ => eq_comm) _

/-- Left ambient generator, in the Lie algebra of the LEFT physical blocks. -/
def balancedLeft (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) : CMat n :=
  blockSkew b₂ ((Z - (1/2 : ℝ) • rightPointProjection b₁ X Z) * Xᴴ)

/-- Right ambient generator, in the Lie algebra of the RIGHT physical blocks. -/
def balancedRight (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) : CMat n :=
  blockSkew b₁ (Xᴴ * (Z - (1/2 : ℝ) • leftPointProjection b₂ X Z))

theorem balancedLeft_supported (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    CSupported b₂ (balancedLeft b₁ b₂ X Z) := blockSkew_supported _ _

theorem balancedRight_supported (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    CSupported b₁ (balancedRight b₁ b₂ X Z) := blockSkew_supported _ _

theorem balancedLeft_skew (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    IsSkewHermitian (balancedLeft b₁ b₂ X Z) := blockSkew_skew _ _

theorem balancedRight_skew (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) :
    IsSkewHermitian (balancedRight b₁ b₂ X Z) := blockSkew_skew _ _

@[simp] theorem balancedLeft_zero (b₁ b₂ : Fin n → ℕ) (X : CMat n) :
    balancedLeft b₁ b₂ X 0 = 0 := by
  simp [balancedLeft, rightPointProjection]

@[simp] theorem balancedRight_zero (b₁ b₂ : Fin n → ℕ) (X : CMat n) :
    balancedRight b₁ b₂ X 0 = 0 := by
  simp [balancedRight, leftPointProjection]

/-- The balanced lift is linear in the ambient direction. -/
@[simp] theorem balancedLeft_smul (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) (a : ℝ) :
    balancedLeft b₁ b₂ X (a • Z) = a • balancedLeft b₁ b₂ X Z := by
  simp [balancedLeft, rightPointProjection, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.sub_mul, blockSkew_sub, smul_sub, smul_smul, mul_comm]

@[simp] theorem balancedRight_smul (b₁ b₂ : Fin n → ℕ) (X Z : CMat n) (a : ℝ) :
    balancedRight b₁ b₂ X (a • Z) = a • balancedRight b₁ b₂ X Z := by
  simp [balancedRight, leftPointProjection, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, blockSkew_sub, smul_sub, smul_smul, mul_comm]

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Smooth

end GS.UnitaryGeometry
