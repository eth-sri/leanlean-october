module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.FreeModule.Basic

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# The primitive-division-module equivalence: equal-characteristic division points are free of rank one

For the standard equal-characteristic Lubin--Tate series, the points killed by
the `(n + 1)`-st iterate form a free rank-one module over
`κ⟦T⟧/(T^(n+1))`.  The shift is intentional: the existing division-tower
The primitive polynomial is indexed by `n`, while its roots lie at division
level `n + 1`.
-/

noncomputable section

open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]





















































































































































































































/-- The coefficient ring at division level `n + 1`. -/
def equalCharacteristicLubinTateTruncatedRing
    (F : LocalField.{u, v} K) (n : ℕ) :=
  F.residueField⟦X⟧ ⧸
    Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)

/-- The commutative ring structure on the named truncated coefficient
ring. -/
instance equalCharacteristicLubinTateTruncatedRing_commRing
    (F : LocalField.{u, v} K) (n : ℕ) :
    CommRing (equalCharacteristicLubinTateTruncatedRing F n) := by
  change CommRing
    (F.residueField⟦X⟧ ⧸
      Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧))
  infer_instance

section
variable (F : LocalField.{u, v} K) (n : ℕ)
include F n
/-- Comparison with the quotient-ring presentation used by the ring
library. -/
def equalCharacteristicLubinTateTruncatedRingEquiv
      :
    equalCharacteristicLubinTateTruncatedRing F n ≃+*
      (F.residueField⟦X⟧ ⧸
        Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)) :=
  RingEquiv.refl _

/-- The canonical projection to the named truncated coefficient ring. -/
def equalCharacteristicLubinTateTruncatedRingMk
       :=
  Ideal.Quotient.mk
    (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧))

/-- Two truncated classes agree exactly when their difference is divisible by `X ^ (n + 1)`. -/
@[simp]
theorem equalCharacteristicLubinTateTruncatedRingMk_eq_iff
      (a b : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateTruncatedRingMk F n a =
        equalCharacteristicLubinTateTruncatedRingMk F n b ↔
      a - b ∈
        Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧) := by
  change
    Ideal.Quotient.mk
        (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)) a =
      Ideal.Quotient.mk
        (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)) b ↔ _
  apply Ideal.Quotient.mk_eq_mk_iff_sub_mem

/-- Every named truncated coefficient has a power-series representative. -/
theorem equalCharacteristicLubinTateTruncatedRingMk_surjective
      :
    Function.Surjective (equalCharacteristicLubinTateTruncatedRingMk F n) := by
  change Function.Surjective
    (Ideal.Quotient.mk
      (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)))
  exact Ideal.Quotient.mk_surjective
end















section
variable {S : Type*} [Semiring S]
    (F : LocalField.{u, v} K) (n : ℕ)
    (f : F.residueField⟦X⟧ →+* S)
    (hf : ∀ a ∈
      Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧),
      f a = 0)
include S F n f hf
/-- Descend a ring homomorphism through the named truncated coefficient
ring. -/
def equalCharacteristicLubinTateTruncatedRingLift
       :=
  (Ideal.Quotient.lift
    (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧))
    f hf).comp
      (equalCharacteristicLubinTateTruncatedRingEquiv F n).toRingHom

/-- A descended homomorphism evaluates a truncated representative by the original map. -/
@[simp]
theorem equalCharacteristicLubinTateTruncatedRingLift_mk
      (a : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateTruncatedRingLift F n f hf
        (equalCharacteristicLubinTateTruncatedRingMk F n a) = f a :=
  rfl
end


/-- The canonical scalar multiplication of the truncated coefficient ring on
itself, named to prevent typeclass search from unfolding the quotient. -/
noncomputable local instance equalCharacteristicLubinTateTruncatedSelfSMul
    (F : LocalField.{u, v} K) (n : ℕ) :
    SMul (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateTruncatedRing F n) where
  smul := (· * ·)

noncomputable local instance equalCharacteristicLubinTateTruncatedSelfModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateTruncatedRing F n) :=
  Semiring.toModule





































































































































































































































































end EqualCharacteristic
end LubinTate

end
