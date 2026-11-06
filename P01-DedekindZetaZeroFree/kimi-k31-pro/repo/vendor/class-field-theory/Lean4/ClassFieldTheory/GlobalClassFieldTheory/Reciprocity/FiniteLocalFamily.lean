module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NormQuotient
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Mathlib.Tactic.NormNum

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Finite local families of ideles

A finite family of local elements, extended by `1`, is the product of its
one-place ideles.  Applying the global norm-quotient map gives the finite
product identity.  The quotient map itself factors through idele classes
and therefore kills principal ideles.
-/

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K : Type*} [Field K] [NumberField K]

/-- A finite local family is the product of its one-place ideles. -/
theorem prod_finitePlaceIdele_eq_ideleOfFiniteLocalFamily
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    (∏ v : ↥S, finitePlaceIdele v.1 (a v)) =
      IdeleGroup.ideleOfFiniteLocalFamily S a := by
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      IdeleGroup.infiniteComponent w
          (∏ v : ↥S, finitePlaceIdele v.1 (a v)) =
        IdeleGroup.infiniteComponent w
          (IdeleGroup.ideleOfFiniteLocalFamily S a)
    rw [map_prod]
    have hfactor :
        ∀ v : ↥S,
          IdeleGroup.infiniteComponent w
              (finitePlaceIdele v.1 (a v)) = 1 := by
      intro v
      exact finitePlaceIdele_infiniteComponent v.1 w (a v)
    have hright :
        IdeleGroup.infiniteComponent w
            (IdeleGroup.ideleOfFiniteLocalFamily S a) = 1 :=
      rfl
    rw [hright]
    simp_rw [hfactor]
    simp
  · apply RestrictedProduct.ext
    intro w
    change
      IdeleGroup.finiteComponent w
          (∏ v : ↥S, finitePlaceIdele v.1 (a v)) =
        (IdeleGroup.ideleOfFiniteLocalFamily S a).2 w
    rw [map_prod]
    by_cases hw : w ∈ S
    · let vw : ↥S := ⟨w, hw⟩
      rw [Finset.prod_eq_single vw]
      · calc
          IdeleGroup.finiteComponent w
              (finitePlaceIdele vw.1 (a vw)) =
              a vw := by
                simpa [vw] using
                  finitePlaceIdele_finiteComponent_same
                    w (a vw)
          _ = (IdeleGroup.ideleOfFiniteLocalFamily S a).2 w :=
            (IdeleGroup.finiteIdeleOfFinset_apply_mem
              S a vw).symm
      · intro b _ hbw
        apply finitePlaceIdele_finiteComponent_of_ne
        grind
      · norm_num
    · calc
        ∏ v : ↥S,
            IdeleGroup.finiteComponent w
              (finitePlaceIdele v.1 (a v)) =
            1 := by
              apply Finset.prod_eq_one
              intro v _
              apply finitePlaceIdele_finiteComponent_of_ne
              grind
        _ = (IdeleGroup.ideleOfFiniteLocalFamily S a).2 w :=
          (IdeleGroup.finiteIdeleOfFinset_apply_notMem
            S a w hw).symm



section NormQuotient

variable
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

local instance finiteLocalFamilyIdeleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance finiteLocalFamilyIdeleClassGroupCommGroup :
    CommGroup (IdeleClassGroup K) :=
  open scoped IsMulCommutative in
  inferInstance



end NormQuotient

end Reciprocity
end GlobalClassFieldTheory

end
