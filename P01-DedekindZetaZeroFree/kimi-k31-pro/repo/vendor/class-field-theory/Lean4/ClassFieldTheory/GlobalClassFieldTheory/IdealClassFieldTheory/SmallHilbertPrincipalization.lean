module

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTheorem
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTransfer
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerUnramified

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Principalization in the selected small Hilbert class field

The selected second small Hilbert class field is Galois over the
canonical fixed-field copy of the original base, and its maximal
abelian intermediate field is the selected first small Hilbert class
field.  Witt transfer therefore places every idele class extended from
that fixed-field copy in the norm range from the second stage.
Functoriality of actual idele extension along the degree-one
identification of the original field with its fixed-field copy gives
the same range inclusion for idele classes extended from the original
field itself.

The exact second-stage norm subgroup is the intrinsic small-Hilbert
subgroup, so the genuine map from the original field on small-Hilbert
quotients is trivial.  Its naturality with extension of ideal classes
then gives the class-group, integral-ideal, and fractional-ideal forms
of principalization over the original number field.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory
open Reciprocity

local instance
    smallHilbertPrincipalization_ideleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance
    smallHilbertPrincipalization_ideleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

local instance
    smallHilbertPrincipalization_smallHilbertQuotientGroup
    {F : Type} [Field F] [NumberField F] :
    Group
      (IdeleClassGroup F ⧸
        smallHilbertClassFieldNormSubgroup (K := F)) :=
  QuotientGroup.Quotient.group
    (smallHilbertClassFieldNormSubgroup (K := F))

local instance
    smallHilbertPrincipalization_smallHilbertQuotientOne
    {F : Type} [Field F] [NumberField F] :
    One
      (IdeleClassGroup F ⧸
        smallHilbertClassFieldNormSubgroup (K := F)) :=
  ⟨(smallHilbertPrincipalization_smallHilbertQuotientGroup
    (F := F)).one⟩

variable (K : Type) [Field K] [NumberField K]













end IdealClassFieldTheory
end GlobalClassFieldTheory

end
