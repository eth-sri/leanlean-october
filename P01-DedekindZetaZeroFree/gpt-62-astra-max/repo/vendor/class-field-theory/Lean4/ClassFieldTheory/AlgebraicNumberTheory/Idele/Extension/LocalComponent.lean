module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Local components of relative adeles and ideles

For a finite place `v` of `K`, evaluation on the finite-adele coordinate is
a `K`-algebra homomorphism `𝔸_K → K_v`.  Scalar extension along `L/K`
therefore gives the actual local component map

`𝔸_K ⊗[K] L → K_v ⊗[K] L`.

This is the map needed to apply the local tensor decomposition and the local
norm calculation to a genuine relative idele.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

section

variable (v : InfinitePlace K)

/-- Evaluation of an adele at an infinite place, as a `K`-algebra
homomorphism. -/
def infiniteAdeleComponentAlgHom :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      v.Completion :=
  (Pi.evalAlgHom K
      (fun w : InfinitePlace K => w.Completion) v).comp
    (AlgHom.fst K
      (NumberField.InfiniteAdeleRing K)
      (FiniteAdeleRing (𝓞 K) K))

@[simp]
theorem infiniteAdeleComponentAlgHom_apply
    (a : NumberField.AdeleRing (𝓞 K) K) :
    infiniteAdeleComponentAlgHom v a = a.1 v :=
  rfl

@[simp]
theorem infiniteAdeleComponentAlgHom_algebraMap (x : K) :
    infiniteAdeleComponentAlgHom v
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) x) =
      algebraMap K v.Completion x :=
  rfl

/-- The relative-adele component at an infinite place:
`𝔸_K ⊗[K] L → K_v ⊗[K] L`. -/
def relativeAdeleInfiniteComponent :
    RelativeAdeleRing K L →ₐ[K]
      v.Completion ⊗[K] L :=
  Algebra.TensorProduct.map
    (infiniteAdeleComponentAlgHom v)
    (AlgHom.id K L)

end

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeAdeleInfiniteComponent_tmul
    (v : InfinitePlace K)
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    relativeAdeleInfiniteComponent v (a ⊗ₜ[K] x) =
      a.1 v ⊗ₜ[K] x := by
  rfl

section

variable (v : HeightOneSpectrum (𝓞 K))

/-- Evaluation of an adele at a finite place, as a `K`-algebra
homomorphism. -/
def finiteAdeleComponentAlgHom :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      v.adicCompletion K :=
  { __ :=
      (RestrictedProduct.evalRingHom
        (fun w : HeightOneSpectrum (𝓞 K) =>
          w.adicCompletion K) v).comp
        (RingHom.snd
          (NumberField.InfiniteAdeleRing K)
          (FiniteAdeleRing (𝓞 K) K))
    commutes' := by
      intro x
      rfl }

@[simp]
theorem finiteAdeleComponentAlgHom_apply
    (a : NumberField.AdeleRing (𝓞 K) K) :
    finiteAdeleComponentAlgHom v a = a.2 v :=
  rfl

@[simp]
theorem finiteAdeleComponentAlgHom_algebraMap (x : K) :
    finiteAdeleComponentAlgHom v
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) x) =
      algebraMap K (v.adicCompletion K) x :=
  rfl

end

omit [NumberField L] [FiniteDimensional K L] in
/-- The relative-adele component at a finite place:
`𝔸_K ⊗[K] L → K_v ⊗[K] L`. -/
def relativeAdeleFiniteComponent
    (v : HeightOneSpectrum (𝓞 K)) :
    RelativeAdeleRing K L →ₐ[K]
      v.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.map
    (finiteAdeleComponentAlgHom v)
    (AlgHom.id K L)

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeAdeleFiniteComponent_tmul
    (v : HeightOneSpectrum (𝓞 K))
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    relativeAdeleFiniteComponent v
        (a ⊗ₜ[K] x) =
      a.2 v ⊗ₜ[K] x := by
  rfl

omit [NumberField K] [NumberField L] in
/-- Determinant norm commutes with scalar extension along a homomorphism
of coefficient algebras.  This is the base-change identity needed to
compare the global relative-idele norm with each local tensor norm. -/
theorem map_norm_tensorProduct_baseChange
    {A : Type*} {B : Type*}
    [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    [Nontrivial A] [Nontrivial B]
    (f : A →ₐ[K] B) (z : A ⊗[K] L) :
    f (Algebra.norm A z) =
      Algebra.norm B
        (Algebra.TensorProduct.map f (AlgHom.id K L) z) := by
  classical
  let b := Module.Free.chooseBasis K L
  have hrepr :
      ∀ i,
        (Algebra.TensorProduct.basis B b).repr
            (Algebra.TensorProduct.map f
              (AlgHom.id K L) z) i =
          f ((Algebra.TensorProduct.basis A b).repr z i) := by
    intro i
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
        simp [map_add, hx, hy]
    | tmul a x =>
        simp
  calc
    _ =
        f
          (MvPolynomial.eval₂ (algebraMap K A)
            ((Algebra.TensorProduct.basis A b).repr z)
            (RelativeIdeleGroup.normPolynomial b)) := by
      rw [RelativeIdeleGroup.eval₂_normPolynomial_baseChange]
    _ =
        MvPolynomial.eval₂
          (f.toRingHom.comp (algebraMap K A))
          (fun i => f
            ((Algebra.TensorProduct.basis A b).repr z i))
          (RelativeIdeleGroup.normPolynomial b) :=
      MvPolynomial.hom_eval₂
        (RelativeIdeleGroup.normPolynomial b)
        (algebraMap K A) f.toRingHom _
    _ =
        MvPolynomial.eval₂ (algebraMap K B)
          ((Algebra.TensorProduct.basis B b).repr
            (Algebra.TensorProduct.map f
              (AlgHom.id K L) z))
          (RelativeIdeleGroup.normPolynomial b) := by
      congr 1
      · simp
      · funext i
        exact (hrepr i).symm
    _ =
        Algebra.norm B
          (Algebra.TensorProduct.map f
            (AlgHom.id K L) z) :=
      RelativeIdeleGroup.eval₂_normPolynomial_baseChange
        B b _

/-- The unit-valued infinite component of a relative idele. -/
def RelativeIdeleGroup.infiniteComponent
    (v : InfinitePlace K) :
    RelativeIdeleGroup K L →*
      (v.Completion ⊗[K] L)ˣ :=
  Units.map
    (relativeAdeleInfiniteComponent
      (K := K) (L := L) v).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem RelativeIdeleGroup.infiniteComponent_coe
    (v : InfinitePlace K)
    (a : RelativeIdeleGroup K L) :
    ((RelativeIdeleGroup.infiniteComponent v a :
        (v.Completion ⊗[K] L)ˣ) :
        v.Completion ⊗[K] L) =
      relativeAdeleInfiniteComponent v
        (a : RelativeAdeleRing K L) :=
  rfl

/-- The unit-valued local component of a relative idele. -/
def RelativeIdeleGroup.finiteComponent
    (v : HeightOneSpectrum (𝓞 K)) :
    RelativeIdeleGroup K L →*
      (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map
    (relativeAdeleFiniteComponent
      (K := K) (L := L) v).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem RelativeIdeleGroup.finiteComponent_coe
    (v : HeightOneSpectrum (𝓞 K))
    (a : RelativeIdeleGroup K L) :
    ((RelativeIdeleGroup.finiteComponent v a :
        (v.adicCompletion K ⊗[K] L)ˣ) :
        v.adicCompletion K ⊗[K] L) =
      relativeAdeleFiniteComponent v
        (a : RelativeAdeleRing K L) :=
  rfl

/-- The determinant norm on the local tensor algebra. -/
def localTensorNorm
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K ⊗[K] L)ˣ →*
      (v.adicCompletion K)ˣ :=
  Units.map (Algebra.norm (v.adicCompletion K))

omit [NumberField L] in
/-- The finite component of the global relative-idele norm is the
determinant norm of the corresponding local tensor component. -/
@[simp]
theorem RelativeIdeleGroup.finiteComponent_norm
    (v : HeightOneSpectrum (𝓞 K))
    (a : RelativeIdeleGroup K L) :
    IdeleGroup.finiteComponent v
        (RelativeIdeleGroup.norm K L a) =
      localTensorNorm (K := K) (L := L) v
        (RelativeIdeleGroup.finiteComponent v a) := by
  apply Units.ext
  exact map_norm_tensorProduct_baseChange
    (finiteAdeleComponentAlgHom v)
    (a : RelativeAdeleRing K L)

omit [NumberField L] in
/-- The infinite component of the global relative-idele norm is the
determinant norm of the corresponding archimedean tensor component. -/
@[simp]
theorem RelativeIdeleGroup.infiniteComponent_norm
    (v : InfinitePlace K)
    (a : RelativeIdeleGroup K L) :
    IdeleGroup.infiniteComponent v
        (RelativeIdeleGroup.norm K L a) =
      Units.map (Algebra.norm v.Completion)
        (RelativeIdeleGroup.infiniteComponent v a) := by
  apply Units.ext
  exact map_norm_tensorProduct_baseChange
    (infiniteAdeleComponentAlgHom v)
    (a : RelativeAdeleRing K L)

/-- Scalar extension of an archimedean base-field unit into its local
tensor algebra. -/
def infiniteLocalIdeleInclusion
    (v : InfinitePlace K) :
    v.Completionˣ →*
      (v.Completion ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := v.Completion) (B := L)).toRingHom

/-- Scalar extension of an extension-field unit into an archimedean
local tensor algebra. -/
def infiniteLocalFieldIdeleInclusion
    (v : InfinitePlace K) :
    Lˣ →* (v.Completion ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeRight
      (R := K) (A := v.Completion)
      (B := L)).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
/-- The infinite component of a globally included idele is scalar
extension of its ordinary infinite component. -/
@[simp]
theorem RelativeIdeleGroup.infiniteComponent_inclusion
    (v : InfinitePlace K)
    (a : IdeleGroup K) :
    RelativeIdeleGroup.infiniteComponent v
        (RelativeIdeleGroup.inclusion K L a) =
      infiniteLocalIdeleInclusion (L := L) v
        (IdeleGroup.infiniteComponent v a) := by
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/-- The infinite component of a principal relative idele is the
diagonal extension-field unit in the local tensor algebra. -/
@[simp]
theorem RelativeIdeleGroup.infiniteComponent_principalIdele
    (v : InfinitePlace K) (x : Lˣ) :
    RelativeIdeleGroup.infiniteComponent v
        (RelativeIdeleGroup.principalIdele K L x) =
      infiniteLocalFieldIdeleInclusion v x := by
  rfl

/-- Scalar extension of a local base-field unit into the local tensor
algebra. -/
def localIdeleInclusion
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →*
      (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := v.adicCompletion K) (B := L)).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
/-- The local component of the globally included idele is the scalar
extension of its ordinary local component. -/
@[simp]
theorem RelativeIdeleGroup.finiteComponent_inclusion
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup K) :
    RelativeIdeleGroup.finiteComponent v
        (RelativeIdeleGroup.inclusion K L a) =
      localIdeleInclusion (L := L) v
        (IdeleGroup.finiteComponent v a) := by
  rfl

/-- Scalar extension of an extension-field unit into the local tensor
algebra. -/
def localFieldIdeleInclusion
    (v : HeightOneSpectrum (𝓞 K)) :
    Lˣ →* (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeRight
      (R := K) (A := v.adicCompletion K)
      (B := L)).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
/-- The local component of a principal relative idele is the diagonal
extension-field unit in the local tensor algebra. -/
@[simp]
theorem RelativeIdeleGroup.finiteComponent_principalIdele
    (v : HeightOneSpectrum (𝓞 K)) (x : Lˣ) :
    RelativeIdeleGroup.finiteComponent v
        (RelativeIdeleGroup.principalIdele K L x) =
      localFieldIdeleInclusion v x := by
  rfl

end
