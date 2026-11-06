module

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Representatives
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Quotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Finite norm-class evaluation after fixed-field inclusion

This compiled leaf preserves the original public declarations while reusing
the shared fixed-field instance providers.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

section RationalIdeleExtension

open Reciprocity
open LocalClassFieldTheory

local instance
    finiteNormClassIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  RationalFiniteNormTransferInternal.ideleClassGroupIsMulCommutative

local instance
    finiteNormClassIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  RationalFiniteNormTransferInternal.ideleClassSubgroupNormal N




end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
