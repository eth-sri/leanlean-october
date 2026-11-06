module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# The small Hilbert class field

The small Hilbert class field corresponds to the image in the idele class
group of the ideles integral at every finite place.  Its reciprocity
quotient is canonically the ordinary ideal class group; consequently its
order is the class number.
-/

open scoped NumberField IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Fix the canonical commutative idèle-class structure used by the Hilbert
class-field quotients in this module. -/
local instance smallHilbertClassFieldIdeleClassGroupIsMulCommutative
    {F : Type*} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The norm subgroup defining the small Hilbert class field.  The
principal subgroup is included before passing to the idele class group so
that the third-isomorphism equivalence applies literally. -/
def smallHilbertClassFieldNormSubgroup :
    Subgroup (IdeleClassGroup K) :=
  Subgroup.map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K))
    (IdeleGroup.integralAtFinitePlaces (K := K) ⊔
      IdeleGroup.principalSubgroup K)

/-- The quotient by the small-Hilbert norm subgroup is the ordinary ideal
class group. -/
def smallHilbertClassFieldQuotientEquivClassGroup :
    IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K) ≃*
      ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientQuotientEquivQuotient
      (IdeleGroup.principalSubgroup K)
      (IdeleGroup.integralAtFinitePlaces (K := K) ⊔
        IdeleGroup.principalSubgroup K)
      le_sup_right).trans
    (IdeleGroup.quotientIntegralSupPrincipalEquiv (K := K))

/-- The small-Hilbert norm subgroup is open. -/
theorem smallHilbertClassFieldNormSubgroup_isOpen :
    IsOpen
      ((smallHilbertClassFieldNormSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) := by
  have hzero :
      (0 : RayClass.Modulus K).ideleCongruenceSubgroup ≤
        IdeleGroup.integralAtFinitePlaces (K := K) :=
    by
      intro a ha
      change a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)
      rw [← RayClass.finiteCongruenceSubgroup_zero (K := K)]
      exact ha.2
  have hden :
      (0 : RayClass.Modulus K).ideleCongruenceSubgroup ≤
        IdeleGroup.integralAtFinitePlaces (K := K) ⊔
          IdeleGroup.principalSubgroup K :=
    hzero.trans le_sup_left
  have hopen :
      IsOpen
        (((IdeleGroup.integralAtFinitePlaces (K := K) ⊔
          IdeleGroup.principalSubgroup K) :
          Subgroup (IdeleGroup K)) :
          Set (IdeleGroup K)) :=
    Subgroup.isOpen_mono hden
      (RayClass.isOpen_ideleCongruenceSubgroup 0)
  rw [smallHilbertClassFieldNormSubgroup, Subgroup.coe_map]
  exact QuotientGroup.isOpenMap_coe _ hopen

/-- The small-Hilbert norm subgroup is closed. -/
theorem smallHilbertClassFieldNormSubgroup_isClosed :
    IsClosed
      ((smallHilbertClassFieldNormSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) :=
  (smallHilbertClassFieldNormSubgroup (K := K)).isClosed_of_isOpen
    smallHilbertClassFieldNormSubgroup_isOpen

/-- The small-Hilbert norm subgroup has finite index. -/
instance smallHilbertClassFieldNormSubgroupFiniteIndex :
    (smallHilbertClassFieldNormSubgroup (K := K)).FiniteIndex := by
  let : Finite
      (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) :=
    Finite.of_equiv (ClassGroup (𝓞 K))
      (smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)).symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient



/-- The big-Hilbert norm subgroup is contained in the small-Hilbert
norm subgroup.  Under class-field duality this is the inclusion of the
small Hilbert class field into the big Hilbert class field. -/
theorem
    bigHilbertClassFieldNormSubgroup_le_smallHilbertClassFieldNormSubgroup :
    bigHilbertClassFieldNormSubgroup (K := K) ≤
      smallHilbertClassFieldNormSubgroup (K := K) := by
  rw [bigHilbertClassFieldNormSubgroup,
    RayClass.Modulus.congruenceSubgroup,
    smallHilbertClassFieldNormSubgroup]
  apply Subgroup.map_mono
  exact sup_le
    ((RayClass.narrowIdeleCongruenceSubgroup_zero_le_integral
      (K := K)).trans le_sup_left)
    le_sup_right

/-- Modulus zero is a defining modulus for the small-Hilbert norm
subgroup. -/
theorem smallHilbertClassFieldNormSubgroup_isDefiningModulus :
    IsDefiningModulus
      (smallHilbertClassFieldNormSubgroup (K := K))
      (0 : RayClass.Modulus K) := by
  have hzero :
      (0 : RayClass.Modulus K).ideleCongruenceSubgroup ≤
        IdeleGroup.integralAtFinitePlaces (K := K) := by
    intro a ha
    change a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)
    rw [← RayClass.finiteCongruenceSubgroup_zero (K := K)]
    exact ha.2
  rw [IsDefiningModulus,
    RayClass.Modulus.congruenceSubgroup,
    smallHilbertClassFieldNormSubgroup]
  exact Subgroup.map_mono (sup_le (hzero.trans le_sup_left) le_sup_right)

/-- The conductorial subgroup supplied by the intrinsic small-Hilbert norm
subgroup and its zero defining modulus. -/
noncomputable def smallHilbertClassFieldConductorialSubgroup :
    ConductorialSubgroup K :=
  ⟨smallHilbertClassFieldNormSubgroup (K := K),
    ⟨0, smallHilbertClassFieldNormSubgroup_isDefiningModulus (K := K)⟩⟩

/-- The canonical quotient transition from the big-Hilbert reciprocity
quotient onto the small-Hilbert reciprocity quotient. -/
noncomputable def
    bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient :
    (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) →*
      (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) :=
  QuotientGroup.map
    (bigHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup (K := K))
    (MonoidHom.id _)
    (show
      bigHilbertClassFieldNormSubgroup (K := K) ≤
        Subgroup.comap (MonoidHom.id _)
          (smallHilbertClassFieldNormSubgroup (K := K)) from by
      intro x hx
      change x ∈ smallHilbertClassFieldNormSubgroup (K := K)
      exact
        bigHilbertClassFieldNormSubgroup_le_smallHilbertClassFieldNormSubgroup
          (K := K) hx)

/-- The big-to-small Hilbert quotient transition sends the class of an
idele class to the same class modulo the larger norm subgroup. -/
@[simp]
theorem bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk
    (x : IdeleClassGroup K) :
    bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
        (K := K)
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)) x) =
      QuotientGroup.mk'
        (smallHilbertClassFieldNormSubgroup (K := K)) x :=
  rfl













/-- The narrow finite conductor of the small-Hilbert norm subgroup is zero. -/
@[simp]
theorem smallHilbertClassField_narrowFiniteConductor :
    (smallHilbertClassFieldConductorialSubgroup
      (K := K)).narrowFiniteConductor = 0 := by
  apply le_antisymm
  · exact
      (smallHilbertClassFieldConductorialSubgroup
        (K := K)).narrowFiniteConductor_le
        (smallHilbertClassFieldNormSubgroup_isDefiningModulus (K := K))
  · exact bot_le

end GlobalClassFields
end GlobalClassFieldTheory

end
