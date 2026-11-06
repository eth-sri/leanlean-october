import GS.MatrixGeometry.Base
noncomputable section
open Matrix InnerProductSpace
namespace GS.MatrixBase
variable {𝕜 : Type} [RCLike 𝕜]
section Rectangular
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
variable (A B C : Matrix ι κ 𝕜)

def cFrobInner : ℝ := ∑ i, ∑ j, RCLike.re (star (A i j)*B i j)
abbrev cFrobSq : ℝ := cFrobInner A A

theorem cFrobInner_eq_re_trace :
    cFrobInner A B = RCLike.re (Matrix.trace (Aᴴ*B)) := by
  simp only [cFrobInner,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Matrix.conjTranspose_apply,map_sum]
  exact Finset.sum_comm

theorem cFrobInner_comm : cFrobInner A B = cFrobInner B A := by
  simp [cFrobInner,RCLike.mul_re,RCLike.star_def,mul_comm]
@[simp] theorem cFrobInner_zero_left : cFrobInner 0 A = 0 := by simp [cFrobInner]
@[simp] theorem cFrobInner_zero_right : cFrobInner A 0 = 0 := by simp [cFrobInner]
theorem cFrobInner_add_left :
    cFrobInner (A+B) C = cFrobInner A C+cFrobInner B C := by
  simp [cFrobInner_eq_re_trace,Matrix.add_mul]
theorem cFrobInner_add_right :
    cFrobInner A (B+C) = cFrobInner A B+cFrobInner A C := by grind [cFrobInner_add_left,cFrobInner_comm]
theorem cFrobInner_neg_left : cFrobInner (-A) B = -cFrobInner A B := by
  simp [cFrobInner_eq_re_trace]
theorem cFrobInner_sub_left :
    cFrobInner (A-B) C = cFrobInner A C-cFrobInner B C := by
  rw [sub_eq_add_neg,cFrobInner_add_left,cFrobInner_neg_left,sub_eq_add_neg]
theorem cFrobInner_real_smul_left (a : ℝ) (A B : Matrix ι κ 𝕜) :
    cFrobInner (a • A) B = a*cFrobInner A B := by
  simp [cFrobInner_eq_re_trace,Matrix.smul_mul,RCLike.smul_re]
theorem cFrobInner_conjTranspose : cFrobInner Aᴴ Bᴴ = cFrobInner A B := by
  simp only [cFrobInner,Matrix.conjTranspose_apply,star_star]
  simp only [RCLike.mul_re,RCLike.star_def,RCLike.conj_re,RCLike.conj_im,
    mul_neg,neg_mul,sub_neg_eq_add]
  exact Finset.sum_comm
theorem cFrobInner_mul_left (A : Matrix ι κ 𝕜) (B : Matrix κ ν 𝕜) (C : Matrix ι ν 𝕜) :
    cFrobInner (A*B) C = cFrobInner B (Aᴴ*C) := by simp_all [cFrobInner_eq_re_trace,Matrix.mul_assoc,Matrix.conjTranspose_mul]
theorem cFrobInner_left_unitary [DecidableEq ι] (U : Matrix ι ι 𝕜)
    (hU : Unitary U) (A B : Matrix ι κ 𝕜) :
    cFrobInner (U*A) (U*B) = cFrobInner A B := by
  rw [cFrobInner_mul_left,← Matrix.mul_assoc,hU.1]; simp
theorem cFrobInner_right_unitary [DecidableEq κ] (U : Matrix κ κ 𝕜)
    (hU : Unitary U) (A B : Matrix ι κ 𝕜) :
    cFrobInner (A*U) (B*U) = cFrobInner A B := by
  simpa only [← Matrix.conjTranspose_mul,cFrobInner_conjTranspose] using
    cFrobInner_left_unitary Uᴴ hU.conjTranspose Aᴴ Bᴴ

instance cFrobCoordinatesRealInner : InnerProductSpace ℝ (EuclideanSpace 𝕜 (ι × κ)) :=
  { InnerProductSpace.rclikeToReal 𝕜 _ with
    toNormedSpace := inferInstance
    smul_left := by
      intro x y r
      change RCLike.re ⟪r • x,y⟫_𝕜 = r*RCLike.re ⟪x,y⟫_𝕜
      rw [inner_smul_left_eq_smul,RCLike.smul_re] }

def encodeCFrob : Matrix ι κ 𝕜 →ₗ[ℝ] EuclideanSpace 𝕜 (ι × κ) where
  toFun A := (WithLp.equiv 2 _).symm (fun k => A k.1 k.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def decodeCFrob : EuclideanSpace 𝕜 (ι × κ) →ₗ[ℝ] Matrix ι κ 𝕜 where
  toFun x i j := x (i,j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem decode_encode_cFrob : decodeCFrob (encodeCFrob A) = A := rfl
@[simp] theorem encode_decode_cFrob (x : EuclideanSpace 𝕜 (ι × κ)) : encodeCFrob (decodeCFrob x) = x := rfl

theorem encodeCFrob_inner : ⟪encodeCFrob A,encodeCFrob B⟫_ℝ = cFrobInner A B := by
  change RCLike.re ⟪encodeCFrob A,encodeCFrob B⟫_𝕜 = _
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,encodeCFrob,
    cFrobInner,Fintype.sum_prod_type,mul_comm]
theorem cFrobSq_nonneg : 0 ≤ cFrobSq A := by
  rw [cFrobSq,← encodeCFrob_inner]
  exact real_inner_self_nonneg
theorem cFrobSq_eq_zero_iff : cFrobSq A = 0 ↔ A = 0 := by
  rw [cFrobSq,← encodeCFrob_inner,inner_self_eq_zero]
  constructor
  · intro h; simpa using congrArg decodeCFrob h
  · rintro rfl; simp
end Rectangular



abbrev CFrobCoordinates (𝕜 : Type) [RCLike 𝕜] (n : ℕ) := EuclideanSpace 𝕜 (Fin n × Fin n)
variable (A B C : KMat 𝕜 n)

def encodedCSubspace (S : Submodule ℝ (KMat 𝕜 n)) : Submodule ℝ (CFrobCoordinates 𝕜 n) :=
  S.map encodeCFrob

/-- An actual continuous linear map, constructed from mathlib's projection.
The name orthogonalProjection follows the mathlib 4.19.0 API. -/
def cFrobProjection (S : Submodule ℝ (KMat 𝕜 n)) : KMat 𝕜 n →L[ℝ] KMat 𝕜 n :=
  ((decodeCFrob : CFrobCoordinates 𝕜 n →ₗ[ℝ] KMat 𝕜 n).toContinuousLinearMap.comp
    ((encodedCSubspace S).subtypeL.comp ((encodedCSubspace S).orthogonalProjection (𝕜 := ℝ)))).comp
    (encodeCFrob : KMat 𝕜 n →ₗ[ℝ] CFrobCoordinates 𝕜 n).toContinuousLinearMap

theorem cFrobProjection_mem (S : Submodule ℝ (KMat 𝕜 n)) (Z : KMat 𝕜 n) :
    cFrobProjection S Z ∈ S := by
  have hp := ((encodedCSubspace S).orthogonalProjection  (encodeCFrob Z)).property
  obtain ⟨A, hA, he⟩ := hp
  change decodeCFrob ((encodedCSubspace S).orthogonalProjection  (encodeCFrob Z) :
    CFrobCoordinates 𝕜 n) ∈ S
  rw [← he, decode_encode_cFrob]
  exact hA

/-- This is the one API-sensitive projection lemma; all later arguments only
use its matrix conclusion. -/
theorem cFrobProjection_normal (S : Submodule ℝ (KMat 𝕜 n)) (Z Y : KMat 𝕜 n)
    (hY : Y ∈ S) : cFrobInner (Z-cFrobProjection S Z) Y = 0 := by
  rw [← encodeCFrob_inner, map_sub]
  exact Submodule.orthogonalProjectionFn_inner_eq_zero (K := encodedCSubspace S)
    (encodeCFrob Z) (encodeCFrob Y) ⟨Y,hY,rfl⟩

theorem cFrobProjection_unique_normal (S : Submodule ℝ (KMat 𝕜 n)) (Z Y : KMat 𝕜 n)
    (hY : Y ∈ S) (hn : ∀ W ∈ S, cFrobInner (Z-Y) W = 0) :
    cFrobProjection S Z = Y := by
  have he := Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (K := encodedCSubspace S) (u := encodeCFrob Z) ⟨Y,hY,rfl⟩ (by
      rintro _ ⟨W,hW,rfl⟩
      simpa only [← map_sub,encodeCFrob_inner] using hn W hW)
  exact congrArg decodeCFrob he

@[simp] theorem cFrobProjection_of_mem (S : Submodule ℝ (KMat 𝕜 n)) (Y : KMat 𝕜 n)
    (hY : Y ∈ S) : cFrobProjection S Y = Y := by
  apply cFrobProjection_unique_normal S Y Y hY
  intro W hW
  simp





theorem cFrobProjection_self_adjoint (S : Submodule ℝ (KMat 𝕜 n)) (A B : KMat 𝕜 n) :
    cFrobInner (cFrobProjection S A) B = cFrobInner A (cFrobProjection S B) := by
  rw [← encodeCFrob_inner,← encodeCFrob_inner]
  exact Submodule.inner_starProjection_left_eq_right (encodedCSubspace S)
    (encodeCFrob A) (encodeCFrob B)


end GS.MatrixBase
