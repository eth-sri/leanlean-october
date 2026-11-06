module

public import Mathlib

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RationalComplexification
public import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Mathlib.FieldTheory.Galois.Abelian

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Complexification of a number field

This module forms the actual compositum with the rational fourth-root field
and proves that restriction to the rational cyclotomic factor is faithful.
-/

open scoped Classical IsMulCommutative
open AlgebraicNumberTheory NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance]
  rationalComplexificationCyclotomicField_isAbelianGalois

 def rationalComplexificationAmbientField :
    IntermediateField ℚ (SeparableClosure ℚ) := by
  letI : Algebra ℚ KummerTheory.rationalCyclotomicField :=
    DivisionRing.toRatAlgebra
  exact IntermediateField.lift rationalComplexificationCyclotomicField

 noncomputable def rationalComplexificationAmbientEquiv :
    rationalComplexificationCyclotomicField ≃ₐ[ℚ]
      rationalComplexificationAmbientField := by
  letI : Algebra ℚ KummerTheory.rationalCyclotomicField :=
    DivisionRing.toRatAlgebra
  exact IntermediateField.liftAlgEquiv
    rationalComplexificationCyclotomicField

variable (F : Type*) [Field F] [NumberField F]

/-- The actual compositum of the chosen copy of `F` with the rational
complexification field inside `SeparableClosure ℚ`. -/
def numberFieldComplexification  :=
  numberFieldInRationalSeparableClosure F ⊔
    rationalComplexificationAmbientField

@[reducible]
noncomputable local instance
    numberFieldComplexificationRationalAlgebra :
    Algebra ℚ (numberFieldComplexification F) :=
  (numberFieldComplexification F).algebra'





















































































 def numberFieldComplexificationBaseLayer :
    IntermediateField ℚ (numberFieldComplexification F) :=
  (numberFieldInRationalSeparableClosure F).restrict
    (le_sup_left)

 def numberFieldComplexificationCyclotomicLayer :
    IntermediateField ℚ (numberFieldComplexification F) :=
  rationalComplexificationAmbientField.restrict
    (le_sup_right)

@[reducible]
noncomputable local instance
    numberFieldComplexificationBaseLayerRationalAlgebra :
    Algebra ℚ (numberFieldComplexificationBaseLayer F) :=
  (numberFieldComplexificationBaseLayer F).algebra'

@[reducible]
noncomputable local instance
    numberFieldComplexificationCyclotomicLayerRationalAlgebra :
    Algebra ℚ (numberFieldComplexificationCyclotomicLayer F) :=
  (numberFieldComplexificationCyclotomicLayer F).algebra'






 noncomputable def numberFieldComplexificationCyclotomicEquiv :
    rationalComplexificationCyclotomicField ≃ₐ[ℚ]
      numberFieldComplexificationCyclotomicLayer F :=
  rationalComplexificationAmbientEquiv.trans
    (IntermediateField.restrictAlgEquiv le_sup_right)

 noncomputable local instance
    numberFieldComplexificationCyclotomicLayer_isAbelianGalois :
    IsAbelianGalois ℚ
      (numberFieldComplexificationCyclotomicLayer F) :=
  IsAbelianGalois.of_algHom
    (numberFieldComplexificationCyclotomicEquiv F).symm.toAlgHom

 noncomputable local instance
    numberFieldComplexificationCyclotomicLayer_isGalois :
    IsGalois ℚ (numberFieldComplexificationCyclotomicLayer F) :=
  (numberFieldComplexificationCyclotomicLayer_isAbelianGalois
    F).toIsGalois

 noncomputable local instance
    numberFieldComplexificationCyclotomicLayer_normal :
    Normal ℚ (numberFieldComplexificationCyclotomicLayer F) :=
  (numberFieldComplexificationCyclotomicLayer_isGalois
    F).to_normal
















































































































































































































































end Reciprocity
end GlobalClassFieldTheory

end
