module

public import Mathlib

public import ValuedFieldTheory.LocalField.Unramified.BaseChangeCore
public import ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# A base-change polynomial model for unramified extensions

Let `L` and `K'` be intermediate fields of a common algebraic ambient field
`Ω`.  Starting from the primitive integral model of a finite unramified
extension `L/K`, this file maps its generator and polynomial to the actual
compositum `L ⊔ K'`.  The resulting data are exactly the inputs of the
primitive-separable integral-model criterion: generation over `K'`, a monic
polynomial vanishing at the mapped generator, and separable reduction.

No finite-dimensionality of `K'/K` is used.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations


section RestrictedValuationMaps

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-- Inclusion of restricted valuation rings along an inclusion of ambient
intermediate fields. -/
def restrictedValuationRingMapOfLE
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    {E F : IntermediateField K Ω} (hEF : E ≤ F) :
    LubinTate.Valuations.exponentialValuationSubring
        (exponentialValuationRestrict w E) →+*
      LubinTate.Valuations.exponentialValuationSubring
        (exponentialValuationRestrict w F) :=
  (IntermediateField.inclusion hEF).toRingHom.restrict _ _ fun x hx ↦ by
    change (0 : WithTop ℝ) ≤ w x
    exact hx

@[simp]
theorem restrictedValuationRingMapOfLE_apply
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    {E F : IntermediateField K Ω} (hEF : E ≤ F)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (exponentialValuationRestrict w E)) :
    ((restrictedValuationRingMapOfLE w hEF x) : F) =
      IntermediateField.inclusion hEF x :=
  rfl

end RestrictedValuationMaps

section BaseChangeModel

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-! The private common-top core retains the source generator together with
its canonical image.  Public projections below expose both the original
primitive integral model and the residue-generator endpoint without
duplicating the base-change proof. -/


































































































































































































































































































































end BaseChangeModel

end Valuations
end AlgebraicNumberTheory

end
