module

public import GS.UnitaryManifold.CayleyAlgebra
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

abbrev kModelSpace (𝕂 : Type) [RCLike 𝕂] {n : ℕ} (block : Fin n → ℕ) :=
  kSupportedSkewSpace 𝕂 block
abbrev KModel (𝕂 : Type) [RCLike 𝕂] {n : ℕ} (block : Fin n → ℕ) := ↥(kModelSpace 𝕂 block)

abbrev modelSpace {n : ℕ} (block : Fin n → ℕ) := kModelSpace ℂ block
abbrev Model {n : ℕ} (block : Fin n → ℕ) := KModel ℂ block

theorem admissible_model {block : Fin n → ℕ} (x : KModel 𝕂 block) :
    admissible x.val := admissible_of_isSkew x.val x.property.2

def kModelInclusion (𝕂 : Type) [RCLike 𝕂] (block : Fin n → ℕ) :
    KModel 𝕂 block →L[ℝ] Matrix (Fin n) (Fin n) 𝕂 :=
  (kModelSpace 𝕂 block).subtypeL

abbrev modelInclusion (block : Fin n → ℕ) := kModelInclusion ℂ (n := n) block

theorem masked_skew_model (block : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) 𝕂) :
    cBlockProjection block (GS.skewHermitianPart A) ∈ kModelSpace 𝕂 block :=
  ⟨fun i j hij => by simp [cBlockProjection, cMask, hij],
   cMask_isSkewHermitian (fun _ _ => eq_comm) (isSkewHermitian_skewHermitianPart A)⟩

def kModelProjectionLinear (𝕂 : Type) [RCLike 𝕂] (block : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) 𝕂 →ₗ[ℝ] KModel 𝕂 block where
  toFun A := ⟨cBlockProjection block (GS.skewHermitianPart A), masked_skew_model block A⟩
  map_add' A B := Subtype.ext ((maskedSkewHermitianMap (fun i j => block i = block j)).map_add A B)
  map_smul' c A := Subtype.ext ((maskedSkewHermitianMap (fun i j => block i = block j)).map_smul c A)

def kModelProjection (𝕂 : Type) [RCLike 𝕂] (block : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) 𝕂 →L[ℝ] KModel 𝕂 block :=
  (kModelProjectionLinear 𝕂 block).toContinuousLinearMap

abbrev modelProjection (block : Fin n → ℕ) := kModelProjection ℂ (n := n) block

@[simp] theorem modelProjection_val (block : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) 𝕂) :
    (kModelProjection 𝕂 block A).val = cBlockProjection block (GS.skewHermitianPart A) := rfl

theorem modelProjection_val_of_mem (block : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) 𝕂)
    (hA : A ∈ kModelSpace 𝕂 block) : (kModelProjection 𝕂 block A).val = A := by
  rw [modelProjection_val, skewHermitianPart_fixed hA.2]
  exact blockProjection_eq_self block A hA.1

@[simp] theorem modelProjection_inclusion (block : Fin n → ℕ) (x : KModel 𝕂 block) :
    kModelProjection 𝕂 block x.val = x :=
  Subtype.ext (modelProjection_val_of_mem block x.val x.property)

end GS.UnitaryManifold
