module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Naturality of the small Hilbert class field

An equivalence of number fields carries the small-Hilbert norm subgroup
exactly onto the small-Hilbert norm subgroup.  Consequently it induces the
canonical equivalence of the corresponding reciprocity quotients.  Transport
of ordinary ideal classes is obtained from this quotient equivalence and is
therefore compatible with the canonical quotient--class-group equivalences.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- Supply the canonical commutativity used by both small-Hilbert quotients. -/
theorem smallHilbertNaturalityIdeleClassIsMulCommutative
    {F : Type*} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] smallHilbertNaturalityIdeleClassIsMulCommutative

variable
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M]

/-- Transport of ordinary idele classes along an equivalence of number
fields carries the small-Hilbert norm subgroup exactly onto the
small-Hilbert norm subgroup of the target. -/
theorem smallHilbertClassFieldNormSubgroup_map_ideleClassCongr
    (e : K ≃ₐ[ℚ] M) :
    (smallHilbertClassFieldNormSubgroup (K := K)).map
        (ideleClassCongr e).toMonoidHom =
      smallHilbertClassFieldNormSubgroup (K := M) := by
  simpa only [smallHilbertClassFieldNormSubgroup,
    IdeleGroup.ordinaryIdealClassSubgroup] using
    ordinaryIdealClassSubgroup_image_map_ideleClassCongr e

/-- The canonical equivalence of small-Hilbert reciprocity quotients induced
by an equivalence of number fields. -/
noncomputable def smallHilbertClassFieldQuotientCongr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) ≃*
      (IdeleClassGroup M ⧸
        smallHilbertClassFieldNormSubgroup (K := M)) :=
  QuotientGroup.congr
    (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup (K := M))
    (ideleClassCongr e)
    (smallHilbertClassFieldNormSubgroup_map_ideleClassCongr e)

/-- On representatives, the small-Hilbert quotient transport is induced by
the existing transport of ordinary idele classes. -/
@[simp]
theorem smallHilbertClassFieldQuotientCongr_mk
    (e : K ≃ₐ[ℚ] M)
    (c : IdeleClassGroup K) :
    smallHilbertClassFieldQuotientCongr e
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K)) c) =
      QuotientGroup.mk'
        (smallHilbertClassFieldNormSubgroup (K := M))
        (ideleClassCongr e c) :=
  rfl




























































































end GlobalClassFields
end GlobalClassFieldTheory

end
