module

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.NormLimitationCore

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Ideal and ray consequences of norm limitation

For a finite extension `L / K`, norm limitation identifies its idèle-class
norm range with that of the maximal abelian subfield in the chosen finite
normal closure.  This leaf transports that equality to the corresponding
ideal norm group for every defining modulus and to the image of the norm
range in every ray class group.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

theorem normLimitationIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] normLimitationIdeleClassIsMulCommutative

variable
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

























































end IdealClassFieldTheory
end GlobalClassFieldTheory

end
