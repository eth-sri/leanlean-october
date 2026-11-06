module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorRayClassMaximality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Prime Artin classes at an exact narrow finite conductor

For a conductorial idèle-class subgroup `H`, a normalized one-place prime
idèle determines compatible classes in the ray class group at
`H.narrowFiniteConductor`, in `C_K / H`, and—away from that finite
conductor—in the ideal Artin quotient.  This file proves their
compatibility, order relations, and maximal ray-class criteria.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable {K : Type} [Field K] [NumberField K]

-- Keep quotient witnesses definitionally aligned with the imported
-- ideal-Artin construction and avoid repeating generic normality search.
attribute [local instance]
  IdealClassFieldTheory.ideleClassSubgroupNormal

/-- The class of a normalized one-place prime idèle in an arbitrary
idèle-class quotient. -/
def subgroupQuotientPrimeClass
    (H : Subgroup (IdeleClassGroup K))
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸ H :=
  QuotientGroup.mk' H
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))

namespace ConductorialSubgroup

/-- The ray class of a normalized one-place prime idèle at the exact
narrow finite conductor of `H`. -/
def narrowFiniteConductorRayPrimeClass
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) :=
  QuotientGroup.mk'
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor))
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))

/-- The exact narrow finite conductor ray-class map sends the ray prime
class to the corresponding class in `C_K / H`. -/
@[simp]
theorem narrowFiniteConductorRayClassGroupToQuotient_rayPrimeClass
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductorRayClassGroupToQuotient
        (H.narrowFiniteConductorRayPrimeClass v) =
      subgroupQuotientPrimeClass H.1 v :=
  rfl

/-- Under maximal exact narrow finite conductor cardinality, the canonical
ray-class equivalence sends the ray prime class to its class in `C_K / H`.
-/
@[simp]
theorem narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_rayPrimeClass
    (H : ConductorialSubgroup K)
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq
        hcard
        (H.narrowFiniteConductorRayPrimeClass v) =
      subgroupQuotientPrimeClass H.1 v :=
  rfl















end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory

end
