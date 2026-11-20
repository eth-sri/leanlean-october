module

public import ClassFieldTheory.AlgebraicNumberTheory.Adele.LocalComponents
public import Mathlib.Algebra.Group.TransferInstance

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# The restricted local product of a relative adele algebra

Using the chosen finite `K`-basis of `L`, a family of local tensor
components comes from `𝔸_K ⊗[K] L` precisely when each basis coefficient
is integral at almost every finite place.  Applying the same condition to
a family of local units and to its pointwise inverse gives an exact
restricted-product model of the relative idele group.

This construction is independent of the later identification of the
chosen-basis lattice with the product of local integer rings.
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

/-- A family of local tensor elements whose chosen-basis coefficients
are integral at almost every finite place. -/
structure RelativeLocalAdeleData where
  /-- The family of archimedean local tensor components. -/
  infinite :
    ∀ w : InfinitePlace K,
      w.Completion ⊗[K] L
  /-- The family of finite local tensor components. -/
  finite :
    ∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L
  /-- Every chosen-basis coefficient of the finite family is integral
  at all but finitely many places. -/
  eventually_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (finite w) i ∈
          w.adicCompletionIntegers K

omit [NumberField L] in
@[ext]
theorem RelativeLocalAdeleData.ext
    {a b : RelativeLocalAdeleData (K := K) (L := L)}
    (hinfinite : a.infinite = b.infinite)
    (hfinite : a.finite = b.finite) :
    a = b := by
  cases a
  cases b
  simp_all

/-- The `i`-th base-adele coefficient assembled from local tensor
coordinates. -/
noncomputable def relativeLocalAdeleCoefficient
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    NumberField.AdeleRing (𝓞 K) K :=
  ⟨fun w =>
      (Algebra.TensorProduct.basis
          w.Completion
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.infinite w) i,
    ⟨fun w =>
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (a.finite w) i,
      a.eventually_integral i⟩⟩

omit [NumberField L] in
@[simp]
theorem relativeLocalAdeleCoefficient_infinite
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L))
    (w : InfinitePlace K) :
    (relativeLocalAdeleCoefficient a i).1 w =
      (Algebra.TensorProduct.basis
          w.Completion
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.infinite w) i :=
  rfl

omit [NumberField L] in
@[simp]
theorem relativeLocalAdeleCoefficient_finite
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeLocalAdeleCoefficient a i).2 w =
      (Algebra.TensorProduct.basis
          (w.adicCompletion K)
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.finite w) i :=
  rfl

/-- Assemble a restricted family of local tensor elements into a
relative adele. -/
noncomputable def relativeAdeleOfLocalData
    (a : RelativeLocalAdeleData (K := K) (L := L)) :
    RelativeAdeleRing K L :=
  relativeAdeleOfCoefficients
    (K := K) (L := L)
    (relativeLocalAdeleCoefficient
      (K := K) (L := L) a)

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_infiniteComponent
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData a) =
      a.infinite w := by
  apply
    (Algebra.TensorProduct.basis
      w.Completion
      (relativeExtensionBasis
         )).repr.injective
  apply Finsupp.ext
  intro i
  simp
  have h :=
    relativeAdeleCoefficient_ofCoefficients

      (relativeLocalAdeleCoefficient
          a) i
  exact congrArg
    (fun q : NumberField.AdeleRing (𝓞 K) K =>
      q.1 w) h

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_finiteComponent
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData a) =
      a.finite w := by
  apply
    (Algebra.TensorProduct.basis
      (w.adicCompletion K)
      (relativeExtensionBasis
         )).repr.injective
  apply Finsupp.ext
  intro i
  simp
  have h :=
    relativeAdeleCoefficient_ofCoefficients

      (relativeLocalAdeleCoefficient
          a) i
  exact congrArg
    (fun q : NumberField.AdeleRing (𝓞 K) K =>
      q.2.1 w) h

/-- Extract every local tensor component of a relative adele, together
with the restrictedness supplied by its base-adele coefficients. -/
noncomputable def relativeAdeleToLocalData
    (z : RelativeAdeleRing K L) :
    RelativeLocalAdeleData (K := K) (L := L) where
  infinite w :=
    relativeAdeleInfiniteComponent
      (K := K) (L := L) w z
  finite w :=
    relativeAdeleFiniteComponent
      (K := K) (L := L) w z
  eventually_integral i := by
    filter_upwards [
      (relativeAdeleCoefficient
          z i).2.2] with w hw
    rw [relativeAdeleFiniteComponent_basis_repr]
    change
      (relativeAdeleCoefficient
          z i).2.1 w ∈
          w.adicCompletionIntegers K at hw ⊢
    exact hw

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_toLocalData
    (z : RelativeAdeleRing K L) :
    relativeAdeleOfLocalData
        (K := K) (L := L)
        (relativeAdeleToLocalData z) =
      z := by
  apply relativeAdele_ext_of_components
  · intro w
    simp
    rfl
  · intro w
    simp
    rfl

/-- A restricted family of local tensor units.  Restrictedness is
required both for the family and for its pointwise inverse. -/
structure RelativeLocalIdeleData where
  /-- The family of archimedean local tensor units. -/
  infinite :
    ∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ
  /-- The family of finite local tensor units. -/
  finite :
    ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ
  /-- Every chosen-basis coefficient of the finite family is integral
  at all but finitely many places. -/
  eventually_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (finite w : w.adicCompletion K ⊗[K] L) i ∈
          w.adicCompletionIntegers K
  /-- Every chosen-basis coefficient of the pointwise inverse finite
  family is integral at all but finitely many places. -/
  eventually_inverse_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (↑((finite w)⁻¹) :
              w.adicCompletion K ⊗[K] L) i ∈
          w.adicCompletionIntegers K

omit [NumberField L] in
@[ext]
theorem RelativeLocalIdeleData.ext
    {a b : RelativeLocalIdeleData (K := K) (L := L)}
    (hinfinite : a.infinite = b.infinite)
    (hfinite : a.finite = b.finite) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Forget local invertibility while retaining the value family. -/
noncomputable def RelativeLocalIdeleData.value
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeLocalAdeleData (K := K) (L := L) where
  infinite w := a.infinite w
  finite w := a.finite w
  eventually_integral := a.eventually_integral

/-- The pointwise inverse family as restricted local adele data. -/
noncomputable def RelativeLocalIdeleData.inverse
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeLocalAdeleData (K := K) (L := L) where
  infinite w :=
    (↑((a.infinite w)⁻¹) :
      w.Completion ⊗[K] L)
  finite w :=
    (↑((a.finite w)⁻¹) :
      w.adicCompletion K ⊗[K] L)
  eventually_integral := a.eventually_inverse_integral

/-- Extract the complete restricted local-unit family of a relative
idele. -/
noncomputable def relativeIdeleToLocalData
    (z : RelativeIdeleGroup K L) :
    RelativeLocalIdeleData (K := K) (L := L) where
  infinite w :=
    RelativeIdeleGroup.infiniteComponent
      (K := K) (L := L) w z
  finite w :=
    RelativeIdeleGroup.finiteComponent
      (K := K) (L := L) w z
  eventually_integral i := by
    filter_upwards [
      (relativeAdeleCoefficient
        (K := K) (L := L)
      (z : RelativeAdeleRing K L) i).2.2] with w hw
    rw [RelativeIdeleGroup.finiteComponent_coe,
      relativeAdeleFiniteComponent_basis_repr]
    change
      (relativeAdeleCoefficient
        (K := K) (L := L)
        (z : RelativeAdeleRing K L) i).2.1 w ∈
          w.adicCompletionIntegers K at hw ⊢
    exact hw
  eventually_inverse_integral i := by
    filter_upwards [
      (relativeAdeleCoefficient
        (K := K) (L := L)
      ((z⁻¹ : RelativeIdeleGroup K L) :
          RelativeAdeleRing K L) i).2.2] with w hw
    rw [← map_inv
      (RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w) z,
      RelativeIdeleGroup.finiteComponent_coe,
      relativeAdeleFiniteComponent_basis_repr]
    change
      (relativeAdeleCoefficient
        (K := K) (L := L)
        ((z⁻¹ : RelativeIdeleGroup K L) :
          RelativeAdeleRing K L) i).2.1 w ∈
          w.adicCompletionIntegers K at hw ⊢
    exact hw

/-- Assemble a restricted local-unit family into a relative idele. -/
noncomputable def relativeIdeleOfLocalData
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeIdeleGroup K L := by
  let x :=
    relativeAdeleOfLocalData
        a.value
  let y :=
    relativeAdeleOfLocalData
        a.inverse
  apply Units.mkOfMulEqOne x y
  apply relativeAdele_ext_of_components
  · intro w
    rw [map_mul,
      relativeAdeleOfLocalData_infiniteComponent,
      relativeAdeleOfLocalData_infiniteComponent,
      map_one]
    change
      (((a.infinite w) * (a.infinite w)⁻¹ :
        (w.Completion ⊗[K] L)ˣ) :
          w.Completion ⊗[K] L) = 1
    simp
  · intro w
    rw [map_mul,
      relativeAdeleOfLocalData_finiteComponent,
      relativeAdeleOfLocalData_finiteComponent,
      map_one]
    change
      (((a.finite w) * (a.finite w)⁻¹ :
        (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L) = 1
    simp

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfLocalData_infiniteComponent
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w
        (relativeIdeleOfLocalData a) =
      a.infinite w := by
  apply Units.ext
  change
    relativeAdeleInfiniteComponent
          w
        (relativeAdeleOfLocalData
            a.value) =
      (a.infinite w :
        w.Completion ⊗[K] L)
  rw [relativeAdeleOfLocalData_infiniteComponent]
  change
    (↑(a.infinite w) :
      w.Completion ⊗[K] L) =
      (↑(a.infinite w) :
        w.Completion ⊗[K] L)
  rfl

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfLocalData_finiteComponent
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (relativeIdeleOfLocalData a) =
      a.finite w := by
  apply Units.ext
  change
    relativeAdeleFiniteComponent
          w
        (relativeAdeleOfLocalData
            a.value) =
      (a.finite w :
        w.adicCompletion K ⊗[K] L)
  rw [relativeAdeleOfLocalData_finiteComponent]
  change
    (↑(a.finite w) :
      w.adicCompletion K ⊗[K] L) =
      (↑(a.finite w) :
        w.adicCompletion K ⊗[K] L)
  rfl

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfLocalData_toLocalData
    (z : RelativeIdeleGroup K L) :
    relativeIdeleOfLocalData
        (K := K) (L := L)
        (relativeIdeleToLocalData z) =
      z := by
  apply relativeIdeleLocalComponents_injective
  apply Prod.ext
  · funext w
    change
      RelativeIdeleGroup.infiniteComponent
            w
          (relativeIdeleOfLocalData

            (relativeIdeleToLocalData
                z)) =
        RelativeIdeleGroup.infiniteComponent
            w z
    simp
    rfl
  · funext w
    change
      RelativeIdeleGroup.finiteComponent
            w
          (relativeIdeleOfLocalData

            (relativeIdeleToLocalData
                z)) =
        RelativeIdeleGroup.finiteComponent
            w z
    simp
    rfl

omit [NumberField L] in
@[simp]
theorem relativeIdeleToLocalData_ofLocalData
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    relativeIdeleToLocalData
        (K := K) (L := L)
        (relativeIdeleOfLocalData a) =
      a := by
  apply RelativeLocalIdeleData.ext
  · funext w
    change
      RelativeIdeleGroup.infiniteComponent
            w
          (relativeIdeleOfLocalData
              a) =
        a.infinite w
    simp
  · funext w
    change
      RelativeIdeleGroup.finiteComponent
            w
          (relativeIdeleOfLocalData
              a) =
        a.finite w
    simp

/-- The relative idele group is exactly the coordinate-restricted
product of all local tensor unit groups. -/
noncomputable def relativeIdeleEquivLocalData :
    RelativeIdeleGroup K L ≃
      RelativeLocalIdeleData (K := K) (L := L) where
  toFun :=
    relativeIdeleToLocalData (K := K) (L := L)
  invFun :=
    relativeIdeleOfLocalData (K := K) (L := L)
  left_inv :=
    relativeIdeleOfLocalData_toLocalData
      (K := K) (L := L)
  right_inv :=
    relativeIdeleToLocalData_ofLocalData
      (K := K) (L := L)

/-- The group structure on the restricted local product, transported
through its proved equivalence with the relative idele group. -/
noncomputable instance relativeLocalIdeleDataGroup :
    Group
      (RelativeLocalIdeleData
        (K := K) (L := L)) :=
  (relativeIdeleEquivLocalData
    (K := K) (L := L)).symm.group

/-- The restricted local-product equivalence as a multiplicative
equivalence. -/
noncomputable def relativeIdeleMulEquivLocalData :
    RelativeIdeleGroup K L ≃*
      RelativeLocalIdeleData (K := K) (L := L) :=
  ((relativeIdeleEquivLocalData
    (K := K) (L := L)).symm.mulEquiv).symm

omit [NumberField L] in
@[simp]
theorem relativeIdeleMulEquivLocalData_apply
    (z : RelativeIdeleGroup K L) :
    relativeIdeleMulEquivLocalData z =
      relativeIdeleToLocalData z :=
  rfl

omit [NumberField L] in
@[simp]
theorem RelativeLocalIdeleData.infinite_mul
    (a b : RelativeLocalIdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    (a * b).infinite w =
      a.infinite w * b.infinite w := by
  change
    RelativeIdeleGroup.infiniteComponent
          w
        (relativeIdeleOfLocalData
              a *
          relativeIdeleOfLocalData
              b) =
      a.infinite w * b.infinite w
  simp

omit [NumberField L] in
@[simp]
theorem RelativeLocalIdeleData.finite_mul
    (a b : RelativeLocalIdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    (a * b).finite w =
      a.finite w * b.finite w := by
  change
    RelativeIdeleGroup.finiteComponent
          w
        (relativeIdeleOfLocalData
              a *
          relativeIdeleOfLocalData
              b) =
      a.finite w * b.finite w
  simp

end
