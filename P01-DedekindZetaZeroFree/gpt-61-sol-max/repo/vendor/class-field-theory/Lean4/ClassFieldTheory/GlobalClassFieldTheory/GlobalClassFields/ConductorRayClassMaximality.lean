module

public import Mathlib

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLattice

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Exact narrow finite conductor ray-class presentations

For a conductorial subgroup `H` of the idèle class group, the ray class
group at its exact narrow finite conductor maps canonically onto `C_K / H`.
This file characterizes injectivity of that map by equality of the two
finite orders and proves uniqueness of subgroups whose exact narrow finite
conductor ray-class presentations are maximal.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type} [Field K] [NumberField K]

/-- Fix the canonical commutative structure used to infer normality of
subgroups of the idèle class group in this module. -/
local instance
    conductorRayClassMaximality_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

namespace ConductorialSubgroup

section
variable (H : ConductorialSubgroup K)
include H
/-- The canonical quotient map from the ray class group at the exact
narrow finite conductor of `H` onto `C_K / H`. -/
noncomputable def narrowFiniteConductorRayClassGroupToQuotient
      :
    RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) →*
      IdeleClassGroup K ⧸ H.1 :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor))
    H.1
    (MonoidHom.id _)
    (show
      RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) ≤
        Subgroup.comap (MonoidHom.id _) H.1 from by
      intro x hx
      change x ∈ H.1
      exact H.narrowFiniteConductor_isDefiningModulus hx)

/-- The exact narrow finite conductor quotient map preserves every
idèle-class representative. -/
@[simp]
theorem narrowFiniteConductorRayClassGroupToQuotient_mk
     
    (c : IdeleClassGroup K) :
    H.narrowFiniteConductorRayClassGroupToQuotient
      (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c) =
      QuotientGroup.mk' H.1 c :=
  rfl

/-- The exact narrow finite conductor ray-class map onto `C_K / H` is
surjective. -/
theorem narrowFiniteConductorRayClassGroupToQuotient_surjective
      :
    Function.Surjective H.narrowFiniteConductorRayClassGroupToQuotient := by
  intro q
  obtain ⟨c, rfl⟩ :=
    QuotientGroup.mk'_surjective H.1 q
  exact
    ⟨QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c,
      rfl⟩





























































































/-- The exact narrow finite conductor ray-class map is injective exactly
when its finite source and target have the same order. -/
theorem narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq
      :
    Function.Injective H.narrowFiniteConductorRayClassGroupToQuotient ↔
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1) := by
  let f := H.narrowFiniteConductorRayClassGroupToQuotient
  have hfSurjective : Function.Surjective f :=
    H.narrowFiniteConductorRayClassGroupToQuotient_surjective
  constructor
  · intro hfInjective
    exact
      Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)
  · intro hcard
    exact
      (hfSurjective.bijective_of_nat_card_le hcard.le).1

/-- When the exact narrow finite conductor ray class group and `C_K / H`
have the same order, the canonical quotient map is a multiplicative
equivalence. -/
noncomputable def narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq
     
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))  :=
  MulEquiv.ofBijective
    H.narrowFiniteConductorRayClassGroupToQuotient
    ⟨H.narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq.2
        hcard,
      H.narrowFiniteConductorRayClassGroupToQuotient_surjective⟩

/-- The maximal exact narrow finite conductor equivalence preserves every
idèle-class representative. -/
@[simp]
theorem narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk
     
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (c : IdeleClassGroup K) :
    H.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq
        hcard
      (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c) =
      QuotientGroup.mk' H.1 c :=
  rfl

/-- A conductorial subgroup is exactly the congruence subgroup at its
narrow finite conductor precisely when its quotient has the full exact
narrow finite conductor ray class number. -/
theorem
    subgroup_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_quotient_card
      :
    H.1 = RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) ↔
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1) := by
  constructor
  · intro hH
    calc
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)).index :=
        (Subgroup.index_eq_card _).symm
      _ = H.1.index := by
        rw [← hH]
      _ = Nat.card (IdeleClassGroup K ⧸ H.1) :=
        Subgroup.index_eq_card H.1
  · intro hcard
    let f := H.narrowFiniteConductorRayClassGroupToQuotient
    have hfInjective : Function.Injective f :=
      H.narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq.2
        hcard
    apply le_antisymm
    · intro c hc
      have hfc :
          f
              (QuotientGroup.mk'
                (RayClass.Modulus.congruenceSubgroup
                  (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c) =
            1 := by
        change QuotientGroup.mk' H.1 c = 1
        exact (QuotientGroup.eq_one_iff _).2 hc
      have hcOne :
          QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup
                (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c =
            1 :=
        hfInjective (hfc.trans (map_one f).symm)
      exact (QuotientGroup.eq_one_iff _).1 hcOne
    · exact H.narrowFiniteConductor_isDefiningModulus
end


section
variable (H J : ConductorialSubgroup K)
    (hconductor : H.narrowFiniteConductor = J.narrowFiniteConductor)
    (hHcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (hJcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ J.1))
include H J hconductor hHcard hJcard
/-- Conductorial subgroups with the same exact narrow finite conductor
and maximal exact-conductor ray-class presentations have equal underlying
subgroups. -/
theorem
    subgroups_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_quotient_cards
      :
    H.1 = J.1 := by
  calc
    H.1 = RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) :=
      H.subgroup_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_quotient_card.2
        hHcard
    _ = RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor) :=
      congrArg
        (fun f => RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite f))
        hconductor
    _ = J.1 :=
      (J.subgroup_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_quotient_card.2
        hJcard).symm

/-- The quotients by two maximal exact narrow finite conductor subgroups
with the same conductor are canonically equivalent. -/
def ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards
      :
    (IdeleClassGroup K ⧸ H.1) ≃*
      (IdeleClassGroup K ⧸ J.1) :=
  QuotientGroup.quotientMulEquivOfEq
    (H.subgroups_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_quotient_cards
      J hconductor hHcard hJcard)

/-- The canonical equivalence between maximal exact narrow finite
conductor quotients preserves every idèle-class representative. -/
@[simp]
theorem
    ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk
     
    (c : IdeleClassGroup K) :
    H.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards
        J hconductor hHcard hJcard
        (QuotientGroup.mk' H.1 c) =
      QuotientGroup.mk' J.1 c :=
  rfl
end


end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory

end
