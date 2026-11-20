module

public import GS.Shared.Basic

public import Mathlib.Analysis.InnerProductSpace.PiL2

public import Mathlib.Analysis.InnerProductSpace.Dual

public import Mathlib.Analysis.Normed.Operator.NormedSpace

public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-! Frobenius calculations use Euclidean coordinates without changing the norm
instances on the ambient matrix space. In particular all projections here are real. -/
noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option backward.isDefEq.respectTransparency false
namespace GS.Shared

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

abbrev FrobCoordinates (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := EuclideanSpace 𝕜 (Fin n × Fin n)

variable (𝕜 n) in
def frobEquiv : M 𝕜 n ≃L[ℝ] FrobCoordinates 𝕜 n :=
  ({ toFun := fun A => (WithLp.equiv 2 _).symm (fun k => A k.1 k.2)
     invFun := fun a i j => a (i, j)
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : M 𝕜 n ≃ₗ[ℝ] FrobCoordinates 𝕜 n).toContinuousLinearEquiv

abbrev encodeFrob := (frobEquiv 𝕜 n).toLinearEquiv.toLinearMap

def frobInner (A B : M 𝕜 n) : ℝ := ⟪frobEquiv 𝕜 n A, frobEquiv 𝕜 n B⟫_ℝ

theorem frobInner_eq_sum (A B : M 𝕜 n) :
    frobInner A B = ∑ i, ∑ j, RCLike.re (star (A i j) * B i j) := by
  simp only [frobInner, PiLp.inner_apply, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    change RCLike.re (B i j * star (A i j)) = _
    rw [mul_comm]

theorem frobInner_eq_trace (A B : M 𝕜 n) : frobInner A B = RCLike.re (Aᴴ * B).trace := by
  rw [frobInner_eq_sum, Matrix.trace, map_sum, Finset.sum_comm]
  simp [Matrix.mul_apply]

theorem frobInner_mul_left (U A B : M 𝕜 n) :
    frobInner (U * A) B = frobInner A (Uᴴ * B) := by
  simp only [frobInner_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem frobInner_mul_right (U A B : M 𝕜 n) :
    frobInner (A * U) B = frobInner A (B * Uᴴ) := by
  grind [frobInner_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm]

theorem frobInner_left_unitary (U : M 𝕜 n) (hU : Unitary U) (A B : M 𝕜 n) :
    frobInner (U * A) (U * B) = frobInner A B := by rw [frobInner_mul_left, hU.adjoint_mul_cancel]

theorem frobInner_right_unitary (U : M 𝕜 n) (hU : Unitary U) (A B : M 𝕜 n) :
    frobInner (A * U) (B * U) = frobInner A B := by
  rw [frobInner_mul_right, Matrix.mul_assoc, hU.2, Matrix.mul_one]

@[simp] theorem frobInner_add_left (A B C : M 𝕜 n) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  simp [frobInner, inner_add_left]

abbrev frobSq (A : M 𝕜 n) := frobInner A A

@[simp] theorem frobInner_add_right (A B C : M 𝕜 n) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  simp [frobInner, inner_add_right]

def encodedSubspace (S : Submodule ℝ (M 𝕜 n)) := S.map encodeFrob

def frobProjection (S : Submodule ℝ (M 𝕜 n)) : M 𝕜 n →L[ℝ] M 𝕜 n :=
  (frobEquiv 𝕜 n).symm.toContinuousLinearMap ∘L (encodedSubspace S).starProjection (𝕜 := ℝ) ∘L
    (frobEquiv 𝕜 n).toContinuousLinearMap

private theorem encode_projection (S : Submodule ℝ (M 𝕜 n)) (Z : M 𝕜 n) :
    frobEquiv 𝕜 n (frobProjection S Z) = (encodedSubspace S).starProjection (𝕜 := ℝ) (frobEquiv 𝕜 n Z) :=
  (frobEquiv 𝕜 n).apply_symm_apply _

theorem frobProjection_mem (S : Submodule ℝ (M 𝕜 n)) (Z : M 𝕜 n) : frobProjection S Z ∈ S := by
  exact (S.mem_map_equiv (e := (frobEquiv 𝕜 n).toLinearEquiv)).mp
    ((encodedSubspace S).starProjection_apply_mem (𝕜 := ℝ) (frobEquiv 𝕜 n Z))

theorem frobProjection_normal (S : Submodule ℝ (M 𝕜 n)) (Z Y : M 𝕜 n) (hY : Y ∈ S) :
    frobInner (Z - frobProjection S Z) Y = 0 := by
  rw [frobInner, map_sub, encode_projection]
  exact Submodule.starProjection_inner_eq_zero (𝕜 := ℝ) _ _ ⟨Y, hY, rfl⟩

theorem frobProjection_of_mem (S : Submodule ℝ (M 𝕜 n)) (Y : M 𝕜 n) (hY : Y ∈ S) :
    frobProjection S Y = Y := (frobEquiv 𝕜 n).injective <|
  (encode_projection S Y).trans ((encodedSubspace S).starProjection_eq_self_iff.mpr ⟨Y,hY,rfl⟩)

theorem frobProjection_inner (S : Submodule ℝ (M 𝕜 n)) (A B : M 𝕜 n) (h : B ∈ S) :
    frobInner (frobProjection S A) B = frobInner A B := by
  exact (sub_eq_zero.mp (by simpa [frobInner, inner_sub_left] using frobProjection_normal S A B h)).symm

/-- Transport the Riesz representative of the real derivative back to matrices. -/
def dualMatrixCLM : (M 𝕜 n →L[ℝ] ℝ) →L[ℝ] M 𝕜 n :=
  (frobEquiv 𝕜 n).symm.toContinuousLinearMap ∘L
    (InnerProductSpace.toDual ℝ (FrobCoordinates 𝕜 n)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (frobEquiv 𝕜 n).symm.toContinuousLinearMap.precomp ℝ

def ambientGradient (f : M 𝕜 n → ℝ) (X : M 𝕜 n) : M 𝕜 n := dualMatrixCLM (fderiv ℝ f X)

theorem ambientGradient_represents (f : M 𝕜 n → ℝ) (X A : M 𝕜 n) :
    fderiv ℝ f X A = frobInner (ambientGradient f X) A := by
  simp [frobInner, ambientGradient, dualMatrixCLM]

theorem ambientGradient_contDiff_of_loss (f : M 𝕜 n → ℝ) {r s : WithTop ℕ∞}
    (hf : ContDiff ℝ s f) (hrs : r + 1 ≤ s) : ContDiff ℝ r (ambientGradient f) := by
  change ContDiff ℝ r ((dualMatrixCLM (n := n) (𝕜 := 𝕜)) ∘ fderiv ℝ f)
  fun_prop

end GS.Shared
