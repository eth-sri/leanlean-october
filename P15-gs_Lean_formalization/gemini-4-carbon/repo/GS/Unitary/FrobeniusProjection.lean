module

public import GS.Unitary.Frobenius
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix InnerProductSpace
open scoped BigOperators
namespace GS.UnitaryGeometry
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

abbrev KFrobCoordinates (𝕂 : Type) [RCLike 𝕂] (n : ℕ) :=
  EuclideanSpace ℝ (Fin n × Fin n × Fin (Module.finrank ℝ 𝕂))
abbrev CFrobCoordinates (n : ℕ) := KFrobCoordinates ℂ n

noncomputable def kRealBasis (𝕂 : Type) [RCLike 𝕂] :
    OrthonormalBasis (Fin (Module.finrank ℝ 𝕂)) ℝ 𝕂 :=
  stdOrthonormalBasis ℝ 𝕂

private theorem kRealBasis_inner (x y : 𝕂) :
    ∑ r, (kRealBasis 𝕂).repr x r * (kRealBasis 𝕂).repr y r = RCLike.re (star x * y) := by
  have h := (kRealBasis 𝕂).repr.inner_map_map x y
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [dotProduct, Pi.star_apply, star_trivial] at h
  have hr : @inner ℝ 𝕂 _ x y = RCLike.re (star x * y) := by
    change RCLike.re (@inner 𝕂 𝕂 _ x y) = _
    simp only [RCLike.inner_apply, RCLike.star_def, mul_comm]
  rw [← hr, ← h]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

def encodeCFrob : Matrix (Fin n) (Fin n) 𝕂 →ₗ[ℝ] KFrobCoordinates 𝕂 n where
  toFun A := (WithLp.equiv 2 _).symm fun k => (kRealBasis 𝕂).repr (A k.1 k.2.1) k.2.2
  map_add' A B := by ext k; simp [map_add]
  map_smul' a A := by ext k; simp [map_smul]

def decodeCFrob : KFrobCoordinates 𝕂 n →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕂 where
  toFun x i j := (kRealBasis 𝕂).repr.symm ((WithLp.equiv 2 _).symm fun r => x (i, j, r))
  map_add' x y := by
    ext i j
    exact (kRealBasis 𝕂).repr.symm.map_add
      ((WithLp.equiv 2 _).symm fun r => x (i, j, r))
      ((WithLp.equiv 2 _).symm fun r => y (i, j, r))
  map_smul' a x := by
    ext i j
    exact (kRealBasis 𝕂).repr.symm.map_smul a ((WithLp.equiv 2 _).symm fun r => x (i, j, r))

@[simp] theorem decode_encode_cFrob (A : Matrix (Fin n) (Fin n) 𝕂) :
    decodeCFrob (encodeCFrob A) = A := by
  ext i j
  change (kRealBasis 𝕂).repr.symm ((kRealBasis 𝕂).repr (A i j)) = A i j
  exact (kRealBasis 𝕂).repr.symm_apply_apply (A i j)

@[simp] theorem encode_decode_cFrob (x : KFrobCoordinates 𝕂 n) :
    encodeCFrob (decodeCFrob x) = x := by
  ext ⟨i, j, r⟩
  have h := (kRealBasis 𝕂).repr.apply_symm_apply ((WithLp.equiv 2 _).symm fun s => x (i, j, s))
  exact congrFun (congrArg (WithLp.equiv 2 _) h) r

theorem encodeCFrob_inner (A B : Matrix (Fin n) (Fin n) 𝕂) :
    ⟪encodeCFrob A, encodeCFrob B⟫_ℝ = cFrobInner A B := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, encodeCFrob, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_prod_type, cFrobInner]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← kRealBasis_inner]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

def encodedCSubspace (S : Submodule ℝ (Matrix (Fin n) (Fin n) 𝕂)) :
    Submodule ℝ (KFrobCoordinates 𝕂 n) :=
  S.map encodeCFrob

def cFrobProjection (S : Submodule ℝ (Matrix (Fin n) (Fin n) 𝕂)) :
    Matrix (Fin n) (Fin n) 𝕂 →L[ℝ] Matrix (Fin n) (Fin n) 𝕂 :=
  ((decodeCFrob : KFrobCoordinates 𝕂 n →ₗ[ℝ] _).toContinuousLinearMap.comp
    ((encodedCSubspace S).subtypeL.comp (encodedCSubspace S).orthogonalProjection)).comp
    (encodeCFrob : Matrix (Fin n) (Fin n) 𝕂 →ₗ[ℝ] _).toContinuousLinearMap

theorem cFrobProjection_mem (S : Submodule ℝ (Matrix (Fin n) (Fin n) 𝕂))
    (Z : Matrix (Fin n) (Fin n) 𝕂) : cFrobProjection S Z ∈ S := by
  obtain ⟨A, hA, he⟩ := ((encodedCSubspace S).orthogonalProjection (encodeCFrob Z)).property
  change decodeCFrob ((encodedCSubspace S).orthogonalProjection (encodeCFrob Z) : KFrobCoordinates 𝕂 n) ∈ S
  rw [← he, decode_encode_cFrob]; exact hA

theorem cFrobProjection_normal (S : Submodule ℝ (Matrix (Fin n) (Fin n) 𝕂))
    (Z Y : Matrix (Fin n) (Fin n) 𝕂) (hY : Y ∈ S) :
    cFrobInner (Z - cFrobProjection S Z) Y = 0 := by
  have hy : encodeCFrob Y ∈ encodedCSubspace S := ⟨Y, hY, rfl⟩
  have h := Submodule.starProjection_inner_eq_zero
    (K := encodedCSubspace S) (encodeCFrob Z) (encodeCFrob Y) hy
  rw [← encodeCFrob_inner, map_sub]
  change ⟪encodeCFrob Z - encodeCFrob (decodeCFrob
    ((encodedCSubspace S).orthogonalProjection (encodeCFrob Z) : KFrobCoordinates 𝕂 n)),
    encodeCFrob Y⟫_ℝ = 0
  rw [encode_decode_cFrob]; exact h

theorem cFrobProjection_unique_normal (S : Submodule ℝ (Matrix (Fin n) (Fin n) 𝕂))
    (Z Y : Matrix (Fin n) (Fin n) 𝕂) (hY : Y ∈ S)
    (hn : ∀ W ∈ S, cFrobInner (Z - Y) W = 0) : cFrobProjection S Z = Y := by
  have hd := S.sub_mem (cFrobProjection_mem S Z) hY
  have h₁ := cFrobProjection_normal S Z _ hd
  have h₂ := hn (cFrobProjection S Z - Y) hd
  apply sub_eq_zero.mp; apply (cFrobSq_eq_zero_iff _).mp
  have he : cFrobProjection S Z - Y = (Z - Y) - (Z - cFrobProjection S Z) := by abel
  change cFrobInner (cFrobProjection S Z - Y) (cFrobProjection S Z - Y) = 0
  conv_lhs => lhs; rw [he]
  rw [cFrobInner_sub_left, h₂, h₁, sub_self]

@[simp] theorem cFrobProjection_of_mem (S : Submodule ℝ (Matrix (Fin n) (Fin n) 𝕂))
    (Y : Matrix (Fin n) (Fin n) 𝕂) (hY : Y ∈ S) : cFrobProjection S Y = Y :=
  cFrobProjection_unique_normal S Y Y hY fun _ _ => by simp

theorem cFrobProjection_self_adjoint (S : Submodule ℝ (Matrix (Fin n) (Fin n) 𝕂))
    (A B : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner (cFrobProjection S A) B = cFrobInner A (cFrobProjection S B) := by
  have ha := cFrobProjection_normal S A _ (cFrobProjection_mem S B)
  have hb := cFrobProjection_normal S B _ (cFrobProjection_mem S A)
  rw [cFrobInner_sub_left] at ha hb
  rw [cFrobInner_comm B, cFrobInner_comm (cFrobProjection S B)] at hb
  linarith

end GS.UnitaryGeometry
