module

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealFrobenius
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Splitting in the small Hilbert class field

The small Hilbert class field has reciprocity quotient the ordinary ideal
class group.  Thus the Frobenius class of a finite prime is its ordinary
ideal class, and it is trivial precisely when the prime ideal is principal.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

/-- Canonical class-group commutativity supplies normality for the quotient. -/
theorem smallHilbertSplittingClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] smallHilbertSplittingClassGroupIsMulCommutative

variable {K : Type*} [Field K] [NumberField K]


















































end IdealClassFieldTheory
end GlobalClassFieldTheory

end
