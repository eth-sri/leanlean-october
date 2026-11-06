module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerConjugation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# The maximal everywhere-unramified abelian subextension

The selected small Hilbert class field is characterized in actual field
order.  Its rational absolute class-formation norm subgroup is exactly
the intrinsic small-Hilbert subgroup of its fixed-field base.  The
order-reversing finite abelian classification then places every actual
finite abelian extension unramified at all finite and infinite places
inside the selected field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open IdealClassFieldTheory LocalClassFieldTheory NumberField Reciprocity

/-- Fix the canonical quotient structure at the boundary between ordinary
idele classes and additive fixed subgroups. -/
@[instance_reducible]
 noncomputable def smallHilbertMaximalSubextensionIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] smallHilbertMaximalSubextensionIdeleClassCommGroup



















































































































































































































































































































end GlobalClassFields
end GlobalClassFieldTheory

end
