module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertNormCharacterization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertNormCharacterization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Maximality criteria for Hilbert class fields

An unramified cyclic extension reaches the big or small Hilbert norm
subgroup exactly when its degree reaches the corresponding narrow or
ordinary class number.  Thus a maximal-degree unramified cyclic
extension has the canonical Hilbert reciprocity quotient.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

theorem hilbertClassFieldMaximalityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] hilbertClassFieldMaximalityIdeleClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

 instance narrowClassGroup_finite :
    Finite (RayClass.NarrowClassGroup K) :=
  Finite.of_equiv
    (RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus K)))
    (RayClass.rayClassGroupNarrowZeroEquivNarrowClassGroup
      (K := K)).toEquiv

 instance bigHilbertNormQuotient_finite :
    Finite
      (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) :=
  Finite.of_equiv
    (RayClass.NarrowClassGroup K)
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm.toEquiv

 instance bigHilbertNormSubgroup_finiteIndex :
    (bigHilbertClassFieldNormSubgroup
      (K := K)).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

























end GlobalClassFields
end GlobalClassFieldTheory

end
