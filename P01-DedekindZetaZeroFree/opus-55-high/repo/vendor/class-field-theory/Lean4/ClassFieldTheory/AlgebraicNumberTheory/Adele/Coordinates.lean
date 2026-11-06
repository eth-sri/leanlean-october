module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.Support

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Coordinate assembly for relative adeles

The chosen finite `K`-basis of `L` identifies
`𝔸_K ⊗[K] L` with a finite family of base adeles.  The support file
constructs and controls the forward coefficients; this file supplies the
inverse assembly map.  It is the global reconstruction half needed when
local tensor components have first been chosen place by place.
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

/-- A relative adele is linearly equivalent to its finite family of
base-adele coefficients in the chosen extension basis. -/
def relativeAdeleCoefficientLinearEquiv :
    RelativeAdeleRing K L ≃ₗ[
      NumberField.AdeleRing (𝓞 K) K]
      (RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K) :=
  (relativeAdeleBasis (K := K) (L := L)).equivFun

omit [NumberField L] in
@[simp]
theorem relativeAdeleCoefficientLinearEquiv_apply
    (z : RelativeAdeleRing K L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    relativeAdeleCoefficientLinearEquiv
        (K := K) (L := L) z i =
      relativeAdeleCoefficient
        (K := K) (L := L) z i :=
  rfl

/-- Assemble a finite family of base adeles into a relative adele. -/
def relativeAdeleOfCoefficients
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K) :
    RelativeAdeleRing K L :=
  (relativeAdeleCoefficientLinearEquiv
    (K := K) (L := L)).symm a

omit [NumberField L] in
@[simp]
theorem relativeAdeleCoefficient_ofCoefficients
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    relativeAdeleCoefficient
        (K := K) (L := L)
        (relativeAdeleOfCoefficients
          (K := K) (L := L) a) i =
      a i := by
  change
    relativeAdeleCoefficientLinearEquiv
        (K := K) (L := L)
        ((relativeAdeleCoefficientLinearEquiv
          (K := K) (L := L)).symm a) i =
      a i
  rw [LinearEquiv.apply_symm_apply]
