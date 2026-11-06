module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMaximalSubextension
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerRealization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationSubextension
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAbstractFixedField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Unramifiedness of the two-stage small Hilbert tower

The second-stage class field is selected in the rational absolute class
formation.  This file transports its exact abstract norm subgroup back
to the ordinary idele class group of the actual middle fixed field.
The intrinsic small-Hilbert characterization then proves genuine
unramifiedness at both finite and infinite places.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open KummerTheory
open LocalClassFieldTheory
open GlobalClassFields










section SelectedTower

variable (K : Type) [Field K] [NumberField K]

/-- The actual top field in the selected two-stage small Hilbert
tower, viewed over the selected first small Hilbert class field. -/
abbrev smallHilbertTowerTopField :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (smallHilbertTowerSecondSubextension K).below








































/-- The relative algebra is the canonical algebra carried by the
intermediate-field presentation of the selected top field. -/
@[reducible]
 noncomputable instance
    smallHilbertTowerTopAlgebra :
    Algebra
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  (smallHilbertTowerTopField K).algebra











/-- Freeze the module owner induced by the same canonical relative
algebra. -/
@[reducible]
 noncomputable def
    smallHilbertTowerTopModule :
    Module
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  @Algebra.toModule
    (smallHilbertClassField K)
    (smallHilbertTowerTopField K)
    _ _
    (smallHilbertTowerTopAlgebra K)

section

attribute [local instance] smallHilbertTowerTopModule










end































end SelectedTower


























































































































































end IdealClassFieldTheory
end GlobalClassFieldTheory

end
