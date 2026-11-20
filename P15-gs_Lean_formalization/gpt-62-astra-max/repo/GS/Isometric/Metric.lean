module

public import GS.Isometric.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-! Transport Hilbert-space duality and projection, without changing the norm on matrices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Matrix InnerProductSpace
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
abbrev Coordinates (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := EuclideanSpace 𝕜 (Fin n × Fin n)
instance : InnerProductSpace ℝ (Coordinates 𝕜 n) :=
  { InnerProductSpace.rclikeToReal 𝕜 _ with
    toNormedSpace := inferInstance
    smul_left := fun x y r => by
      change RCLike.re (inner 𝕜 (r • x) y) = r * RCLike.re (inner 𝕜 x y)
      rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul] }

def encode : Square 𝕜 n ≃L[ℝ] Coordinates 𝕜 n := LinearEquiv.toContinuousLinearEquiv
  { toFun A := WithLp.toLp 2 fun k => A k.1 k.2
    invFun x i j := x (i,j)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    left_inv _ := rfl
    right_inv _ := rfl }

def pairing (A B : Square 𝕜 n) : ℝ := ⟪encode A, encode B⟫_ℝ

lemma pairing_trace (A B : Square 𝕜 n) : pairing A B = RCLike.re (Aᴴ * B).trace := by
  change RCLike.re (∑ k : Fin n × Fin n, B k.1 k.2 * star (A k.1 k.2)) = _
  simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1; rw [Finset.sum_comm]; simp only [mul_comm]

lemma pairing_left_unitary (U : Square 𝕜 n) (h : IsU U) (A B : Square 𝕜 n) :
    pairing (U*A) (U*B) = pairing A B := by
  simp only [pairing_trace, Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
  grind
lemma pairing_right_unitary (U : Square 𝕜 n) (h : IsU U) (A B : Square 𝕜 n) :
    pairing (A*U) (B*U) = pairing A B := by
  simp only [pairing_trace, Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.2, Matrix.one_mul]

variable (S : Submodule ℝ (Square 𝕜 n))

def projection : Square 𝕜 n →L[ℝ] Square 𝕜 n :=
  encode.symm.toContinuousLinearMap ∘L (S.map encode.toLinearMap).starProjection ∘L encode.toContinuousLinearMap

lemma encode_projection (Z : Square 𝕜 n) : encode (projection S Z) = (S.map encode.toLinearMap).starProjection (encode Z) :=
  encode.apply_symm_apply _

lemma projection_mem (Z : Square 𝕜 n) : projection S Z ∈ S := by
  obtain ⟨Y,hY,he⟩ := (S.map encode.toLinearMap).starProjection_apply_mem (encode Z)
  rwa [show projection S Z = Y from encode.injective ((encode_projection S Z).trans he.symm)]
lemma projection_normal (Z Y : Square 𝕜 n) (hY : Y ∈ S) : pairing (Z-projection S Z) Y = 0 := by
  rw [pairing, map_sub, encode_projection]
  simp_all
@[simp] lemma projection_of_mem (Y : Square 𝕜 n) (hY : Y ∈ S) : projection S Y = Y := by
  apply encode.injective; rw [encode_projection,Submodule.starProjection_eq_self_iff]; exact ⟨_,hY,rfl⟩
lemma projection_self_adjoint (A B : Square 𝕜 n) : pairing (projection S A) B = pairing A (projection S B) := by
  simp only [pairing, encode_projection]; apply Submodule.inner_starProjection_left_eq_right

/-- The Riesz representative of an ambient real covector. -/
def riesz : (Square 𝕜 n →L[ℝ] ℝ) →L[ℝ] Square 𝕜 n :=
  let e := (encode (𝕜 := 𝕜) (n := n)).symm.toContinuousLinearMap
  e ∘L (toDual ℝ (Coordinates 𝕜 n)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (ContinuousLinearMap.compL ℝ (Coordinates 𝕜 n) (Square 𝕜 n) ℝ).flip e

def ambientGradient (f : Square 𝕜 n → ℝ) (X : Square 𝕜 n) := riesz (fderiv ℝ f X)
lemma ambientGradient_represents (f : Square 𝕜 n → ℝ) (X V : Square 𝕜 n) :
    fderiv ℝ f X V = pairing (ambientGradient f X) V := by
  simpa [pairing, ambientGradient, riesz] using
    (toDual_symm_apply (x := encode V) (y := (fderiv ℝ f X).comp encode.symm.toContinuousLinearMap)).symm

lemma ambientGradient_contDiff_of_loss (f : Square 𝕜 n → ℝ) {r s : WithTop ℕ∞}
    (hf : ContDiff ℝ s f) (hrs : r + 1 ≤ s) : ContDiff ℝ r (ambientGradient f) :=
by
  unfold ambientGradient
  exact ContDiff.comp (g := ⇑(riesz (𝕜 := 𝕜) (n := n))) (f := fderiv ℝ f) (ContinuousLinearMap.contDiff _) (hf.fderiv_right hrs)

end GS.Isometric
