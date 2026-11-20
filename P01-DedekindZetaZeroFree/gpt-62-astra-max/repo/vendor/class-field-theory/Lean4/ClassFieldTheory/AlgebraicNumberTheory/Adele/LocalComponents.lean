module

public import ClassFieldTheory.AlgebraicNumberTheory.Adele.Coordinates

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Joint local components of relative adeles and ideles

The archimedean and finite tensor components jointly determine an element
of `𝔸_K ⊗[K] L`.  This file records the corresponding injective
homomorphism on relative ideles.  Surjectivity onto the restricted local
product is handled separately, once integral compatibility with the local
tensor decomposition has been established.
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

omit [NumberField L] in
/-- A local tensor component has the expected chosen-basis
coordinates at a finite place. -/
@[simp]
theorem relativeAdeleFiniteComponent_basis_repr
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        (w.adicCompletion K)
        (relativeExtensionBasis
          (K := K) (L := L))).repr
        (relativeAdeleFiniteComponent w z) i =
      (relativeAdeleCoefficient z i).2 w := by
  classical
  rw [relativeAdeleFiniteComponent_eq_sum_tmul_coefficients]
  simp [relativeExtensionBasis, Finsupp.single_apply]

omit [NumberField L] in
/-- A local tensor component has the expected chosen-basis
coordinates at an infinite place. -/
@[simp]
theorem relativeAdeleInfiniteComponent_basis_repr
    (z : RelativeAdeleRing K L)
    (w : InfinitePlace K)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        w.Completion
        (relativeExtensionBasis
          (K := K) (L := L))).repr
        (relativeAdeleInfiniteComponent w z) i =
      (relativeAdeleCoefficient z i).1 w := by
  classical
  rw [relativeAdeleInfiniteComponent_eq_sum_tmul_coefficients]
  simp [relativeExtensionBasis, Finsupp.single_apply]
  change
    (relativeAdeleCoefficient
          z i).1 w *
        algebraMap K w.Completion (1 : K) =
      (relativeAdeleCoefficient
          z i).1 w
  simp [map_one]

omit [NumberField L] in
/-- Equality of every archimedean and finite tensor component implies
equality of relative adeles. -/
theorem relativeAdele_ext_of_components
    {x y : RelativeAdeleRing K L}
    (hinfinite :
      ∀ w : InfinitePlace K,
        relativeAdeleInfiniteComponent w x =
          relativeAdeleInfiniteComponent w y)
    (hfinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        relativeAdeleFiniteComponent w x =
          relativeAdeleFiniteComponent w y) :
    x = y := by
  apply
    (relativeAdeleCoefficientLinearEquiv
       ).injective
  funext i
  apply Prod.ext
  · funext w
    have h :=
      congrArg
        (fun z =>
          (Algebra.TensorProduct.basis
            w.Completion
            (relativeExtensionBasis
               )).repr z i)
        (hinfinite w)
    change (relativeAdeleCoefficient x i).1 w =
      (relativeAdeleCoefficient y i).1 w
    simpa using h
  · apply DFunLike.coe_injective
    funext w
    have h :=
      congrArg
        (fun z =>
          (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
               )).repr z i)
        (hfinite w)
    change (relativeAdeleCoefficient x i).2 w =
      (relativeAdeleCoefficient y i).2 w
    simpa using h

/-- The unrestricted family of every archimedean and finite local
tensor unit group. -/
abbrev RelativeLocalTensorFamily :=
  (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ×
    (∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ)

/-- All local tensor components of a relative idele. -/
def relativeIdeleLocalComponents :
    RelativeIdeleGroup K L →*
      RelativeLocalTensorFamily (K := K) (L := L) where
  toFun z :=
    ⟨fun w =>
        RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w z,
      fun w =>
        RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z⟩
  map_one' := by
    apply Prod.ext
    · funext w
      exact map_one
        (RelativeIdeleGroup.infiniteComponent
            w)
    · funext w
      exact map_one
        (RelativeIdeleGroup.finiteComponent
            w)
  map_mul' x y := by
    apply Prod.ext
    · funext w
      exact map_mul
        (RelativeIdeleGroup.infiniteComponent
            w) x y
    · funext w
      exact map_mul
        (RelativeIdeleGroup.finiteComponent
            w) x y

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeIdeleLocalComponents_infinite
    (z : RelativeIdeleGroup K L)
    (w : InfinitePlace K) :
    (relativeIdeleLocalComponents z).1 w =
      RelativeIdeleGroup.infiniteComponent w z :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeIdeleLocalComponents_finite
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeIdeleLocalComponents z).2 w =
      RelativeIdeleGroup.finiteComponent w z :=
  rfl

omit [NumberField L] in
/-- The complete local-component map is injective. -/
theorem relativeIdeleLocalComponents_injective :
    Function.Injective
      (relativeIdeleLocalComponents
        (K := K) (L := L)) := by
  intro x y hxy
  apply Units.ext
  apply relativeAdele_ext_of_components
  · intro w
    exact congrArg Units.val (congrArg (fun z => z.1 w) hxy)
  · intro w
    exact congrArg Units.val (congrArg (fun z => z.2 w) hxy)

end
