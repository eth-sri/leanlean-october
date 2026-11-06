module

public import GS.Continuation.AmbientProjection
public import GS.CayleyCharts.Model
public import GS.Extensions.MatrixCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A canonical, point-only split of a GS tangent direction, including overlap

The original checked pointProjection is unchanged. The left and right orbit
projectors commute on the actual GS family. Subtracting half of their common
part produces supported skew generators directly from (X,Z), without choosing
factors. No no-overlap or sharing hypothesis is hidden here: arbitrary overlap
is allowed, but independent physical blocks are assumed.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable
open Matrix GS GS.Extensions GS.Continuation GS.CayleyCharts
open scoped Topology
namespace GS.GlobalGeometry
variable {n : ℕ}

@[simp] theorem blockSkew_add (b : Fin n → ℕ) (A B : Mat n) :
    blockSkew b (A+B) = blockSkew b A + blockSkew b B := by
  ext i j
  by_cases h : b i = b j <;> simp [blockSkew, maskedSkew, mask, skew, h] <;> ring

@[simp] theorem blockSkew_smul (b : Fin n → ℕ) (a : ℝ) (A : Mat n) :
    blockSkew b (a • A) = a • blockSkew b A := by
  ext i j
  by_cases h : b i = b j <;> simp [blockSkew, maskedSkew, mask, skew, h] <;> ring

@[simp] theorem blockSkew_zero (b : Fin n → ℕ) : blockSkew b (0 : Mat n) = 0 := by
  ext i j
  simp [blockSkew, maskedSkew, mask, skew]

theorem blockSkew_sub (b : Fin n → ℕ) (A B : Mat n) :
    blockSkew b (A-B) = blockSkew b A - blockSkew b B := by
  ext i j
  by_cases h : b i = b j <;> simp [blockSkew, maskedSkew, mask, skew, h] <;> ring

theorem blockSkew_supported (b : Fin n → ℕ) (A : Mat n) :
    Supported b (blockSkew b A) := (masked_skew_model b A).1

theorem blockSkew_skew (b : Fin n → ℕ) (A : Mat n) :
    IsSkew (blockSkew b A) := (masked_skew_model b A).2

/-- Left ambient generator, in the Lie algebra of the LEFT physical blocks. -/
def balancedLeft (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) : Mat n :=
  blockSkew b₂ ((Z - (1/2 : ℝ) • rightPointProjection b₁ X Z) * Xᵀ)

/-- Right ambient generator, in the Lie algebra of the RIGHT physical blocks. -/
def balancedRight (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) : Mat n :=
  blockSkew b₁ (Xᵀ * (Z - (1/2 : ℝ) • leftPointProjection b₂ X Z))

theorem balancedLeft_supported (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    Supported b₂ (balancedLeft b₁ b₂ X Z) := blockSkew_supported _ _

theorem balancedRight_supported (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    Supported b₁ (balancedRight b₁ b₂ X Z) := blockSkew_supported _ _

theorem balancedLeft_skew (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    IsSkew (balancedLeft b₁ b₂ X Z) := blockSkew_skew _ _

theorem balancedRight_skew (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) :
    IsSkew (balancedRight b₁ b₂ X Z) := blockSkew_skew _ _

@[simp] theorem balancedLeft_zero (b₁ b₂ : Fin n → ℕ) (X : Mat n) :
    balancedLeft b₁ b₂ X 0 = 0 := by
  simp [balancedLeft, rightPointProjection]

@[simp] theorem balancedRight_zero (b₁ b₂ : Fin n → ℕ) (X : Mat n) :
    balancedRight b₁ b₂ X 0 = 0 := by
  simp [balancedRight, leftPointProjection]

/-- The balanced lift is linear in the ambient direction. -/
@[simp] theorem balancedLeft_smul (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) (a : ℝ) :
    balancedLeft b₁ b₂ X (a • Z) = a • balancedLeft b₁ b₂ X Z := by
  simp [balancedLeft, rightPointProjection, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.sub_mul, blockSkew_sub, smul_sub, smul_smul, mul_comm]

@[simp] theorem balancedRight_smul (b₁ b₂ : Fin n → ℕ) (X Z : Mat n) (a : ℝ) :
    balancedRight b₁ b₂ X (a • Z) = a • balancedRight b₁ b₂ X Z := by
  simp [balancedRight, leftPointProjection, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, blockSkew_sub, smul_sub, smul_smul, mul_comm]

end GS.GlobalGeometry
