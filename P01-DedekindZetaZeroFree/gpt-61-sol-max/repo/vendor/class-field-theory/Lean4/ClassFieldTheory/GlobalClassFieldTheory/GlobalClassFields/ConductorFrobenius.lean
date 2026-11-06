module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclicRayClassMaximality
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealFrobenius

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Prime classes at the narrow finite norm conductor

The one-place idèle of normalized order one defines two compatible
prime classes: one in the ray class group at the exact narrow finite norm
conductor, and one in the actual idele-class norm quotient.  The
canonical narrow-finite-conductor ray-class map sends the former to the latter.

For cyclic extensions the order of the norm-quotient class divides the
extension degree.  Complete splitting forces this class to be trivial;
when the narrow-finite-conductor ray-class presentation is maximal, it also
forces the narrow finite conductor ray prime class itself to be trivial.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

-- Reuse the normality witness embedded in the imported ideal-Artin maps.
-- Without it, every occurrence of the norm quotient repeats an expensive
-- unsuccessful instance search and builds a non-definitional witness.
attribute [local instance]
  IdealClassFieldTheory.ideleClassSubgroupNormal

/-- The class of the normalized one-place prime idèle in the ray class
group at the exact narrow finite conductor of the actual norm subgroup. -/
def narrowFiniteConductorRayPrimeClass
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) :=
  QuotientGroup.mk'
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L))))
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))

/-- The class of the normalized one-place prime idèle in the actual
idele-class norm quotient. -/
def ideleClassNormFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸
      (_root_.ideleClassNorm K L).range :=
  QuotientGroup.mk'
    ((_root_.ideleClassNorm K L).range)
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))




























































































































/-- The canonical narrow-finite-conductor ray-class map sends the narrow
finite conductor ray prime class to the corresponding actual norm-quotient
Frobenius class. -/
@[simp]
theorem
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass
    (v : HeightOneSpectrum (𝓞 K)) :
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
        (K := K) (L := L)
        (narrowFiniteConductorRayPrimeClass
          (K := K) (L := L) v) =
      ideleClassNormFrobeniusClass
        (K := K) (L := L) v :=
  rfl
















































































































































































































section Cyclic

variable [IsCyclic (L ≃ₐ[K] L)]











































































































































end Cyclic






















end GlobalClassFields
end GlobalClassFieldTheory

end
