module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuationUniformizer
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuedExtensionUnitMap
public import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Principal-unit decomposition

This file connects the principal-unit decomposition proved in
`PrincipalUnits` to the standard integer-valued field-unit valuation attached
to a `ℤᵐ⁰`-valued complete discrete valuation.
-/

noncomputable section

open Filter
open scoped Topology
open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

variable {K : Type u} [Field K]

section

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))

/-- The uniformizer–residue–principal-unit decomposition, group-isomorphism form for a complete
DVF with a fixed uniformizer:
`K^* ≃ μ_{q-1} × U^1 × ℤ`. -/
noncomputable def fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF :
    fieldUnitDecompositionFactors F ≃* Kˣ := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F)
        hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  exact
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_zeroSubgroup_eq_unitGroup
      (F := F) V hzero hπV

/--
The defining evaluation formula for `fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF`
is `fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ z =
valuationSubringUnitFieldUnitHom F (z.1.1 : F.valuationSubringˣ) *
valuationSubringUnitFieldUnitHom F (z.1.2 : F.valuationSubringˣ) * (Units.mk0 (π : K) hπ.ne_zero)
^ Multiplicative.toAdd z.2`.
-/
@[simp]
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply
    (z : fieldUnitDecompositionFactors F) :
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ z =
      valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) *
        (Units.mk0 (π : K) hπ.ne_zero) ^ Multiplicative.toAdd z.2 := by
  rfl

/--
Establishes the identity `((CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).val
(fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ z) = Multiplicative.toAdd z.2`.
-/
@[simp]
theorem multiplicativeIntegerValuationOfUniformizer_fieldUnitsEquivRootsPrincipalUnitsUniformizer
    (z : fieldUnitDecompositionFactors F) :
    ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).val
        (fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
          F hπ z) =
      Multiplicative.toAdd z.2 := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          valuationSubringUnitFieldUnitHom F u = y := fun y => mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
        (F := F) V
        (by
          simpa using
            (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F) hπ)
        y
  refine V.valuation_uniformizer_normal_form ?_ ((hzero _).2
    ⟨(z.1.1 : F.valuationSubringˣ) * (z.1.2 : F.valuationSubringˣ), by
      rw [map_mul]⟩) (Multiplicative.toAdd z.2)
  simpa using
  (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ

/--
Establishes the identity `(CompleteDVF.uniformizerValueExponent F) hπ
(fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ z) = Multiplicative.toAdd z.2`.
-/
@[simp]
theorem uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer
    (z : fieldUnitDecompositionFactors F) :
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ
        (fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
          F hπ z) =
      Multiplicative.toAdd z.2 :=
  multiplicativeIntegerValuationOfUniformizer_fieldUnitsEquivRootsPrincipalUnitsUniformizer
    F hπ z

/--
Establishes the identity `Multiplicative.toAdd
((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ).symm x).2 =
(CompleteDVF.uniformizerValueExponent F) hπ x`.
-/
@[simp]
theorem uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm
    (x : Kˣ) :
    Multiplicative.toAdd
        ((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
          F hπ).symm x).2 =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x := by
  have h :=
    uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer
      F hπ
      ((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ).symm x)
  simpa using h.symm

/--
Establishes the identity `((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F
hπ).symm x).2 = Multiplicative.ofAdd ((CompleteDVF.uniformizerValueExponent F) hπ x)`.
-/
@[simp]
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_snd
    (x : Kˣ) :
    ((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ).symm x).2 =
      Multiplicative.ofAdd ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x) := by
  let E :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  have h :
      Multiplicative.toAdd ((E.symm x).2) =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x := by
    simp [E]
  exact h

/--
`fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_factors_mul_uniformizer` satisfies the
integer-power formula `valuationSubringUnitFieldUnitHom F
(((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ).symm x).1.1 :
F.valuationSubringˣ) * valuationSubringUnitFieldUnitHom F
(((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ).symm x).1.2 :
F.valuationSubringˣ) * (Units.mk0 (π : K) hπ.ne_zero) ^ (CompleteDVF.uniformizerValueExponent F)
hπ x = x`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_factors_mul_uniformizer_zpow
    (x : Kˣ) :
    valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
            F hπ).symm x).1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
            F hπ).symm x).1.2 : F.valuationSubringˣ) *
        (Units.mk0 (π : K) hπ.ne_zero) ^ (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x =
      x := by
  let E :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  have hexp :
      Multiplicative.toAdd ((E.symm x).2) =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x := by
    simp [E]
  calc
    valuationSubringUnitFieldUnitHom F
          (((E.symm x).1.1 : F.valuationSubringˣ)) *
        valuationSubringUnitFieldUnitHom F
          (((E.symm x).1.2 : F.valuationSubringˣ)) *
        (Units.mk0 (π : K) hπ.ne_zero) ^ (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x =
        valuationSubringUnitFieldUnitHom F
            (((E.symm x).1.1 : F.valuationSubringˣ)) *
          valuationSubringUnitFieldUnitHom F
            (((E.symm x).1.2 : F.valuationSubringˣ)) *
          (Units.mk0 (π : K) hπ.ne_zero) ^ Multiplicative.toAdd ((E.symm x).2) := by
          rw [hexp]
    _ = E (E.symm x) := by
          rfl
    _ = x := E.apply_symm_apply x

/--
`fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitPart_eq_mul_uniformizer_zpow` satisfies
the negation formula `valuationSubringUnitFieldUnitHom F
(((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ).symm x).1.1 :
F.valuationSubringˣ) * valuationSubringUnitFieldUnitHom F
(((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ).symm x).1.2 :
F.valuationSubringˣ) = x * (Units.mk0 (π : K) hπ.ne_zero) ^
(-((CompleteDVF.uniformizerValueExponent F) hπ x))`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitPart_eq_mul_uniformizer_zpow_neg
    (x : Kˣ) :
    valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
            F hπ).symm x).1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
            F hπ).symm x).1.2 : F.valuationSubringˣ) =
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) := by
  let ϖ := Units.mk0 (π : K) hπ.ne_zero
  let u :=
    valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
            F hπ).symm x).1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
            F hπ).symm x).1.2 : F.valuationSubringˣ)
  have hux :
      u * ϖ ^ (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x = x := by
    simpa [u, ϖ] using
      fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_factors_mul_uniformizer_zpow
        F hπ x
  calc
    u = u * 1 := by simp
    _ = u * (ϖ ^ (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x *
        ϖ ^ (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x))) := by
          simp
    _ = x * ϖ ^ (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) := by
          rw [← mul_assoc, hux]

end

section

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) {π : F.valuationSubring}
    (hπ : F.valuation.IsUniformizer (π : K)) (x : Kˣ)

/--
Establishes the membership statement `x * (Units.mk0 (π : K) hπ.ne_zero) ^
(-((CompleteDVF.uniformizerValueExponent F) hπ x)) ∈ F.valuation.valuationSubring.unitGroup`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_unitPart_mem_unitGroup :
    x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) ∈
      F.valuation.valuationSubring.unitGroup := by
  let V :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero :
      V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F) hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  have hmem :
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
          (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) ∈
        V.zeroSubgroup := by
    rw [V.mem_zeroSubgroup_iff, V.val_mul, V.val_uniformizer_zpow hπV]
    simp [V]
  simpa [hzero] using hmem

/-- The valuation-ring unit obtained by removing the uniformizer power from a
field unit. -/
noncomputable def fieldUnitUniformizerUnitPart : F.valuationSubringˣ :=
  F.valuation.valuationSubring.unitGroupMulEquiv
    ⟨x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)),
      fieldUnitsEquivRootsPrincipalUnitsUniformizer_unitPart_mem_unitGroup
        F hπ x⟩

/--
Establishes the identity `valuationSubringUnitFieldUnitHom F (fieldUnitUniformizerUnitPart F hπ x)
= x * (Units.mk0 (π : K) hπ.ne_zero) ^ (-((CompleteDVF.uniformizerValueExponent F) hπ x))`.
-/
@[simp]
theorem valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart :
    valuationSubringUnitFieldUnitHom F
        (fieldUnitUniformizerUnitPart F hπ x) =
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) := by
  rfl

end

section

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) (x : Kˣ)

/--
Establishes the identity `(((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F
hπ).symm x).1.1 : F.valuationSubringˣ) *
(((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ).symm x).1.2 :
F.valuationSubringˣ) = fieldUnitUniformizerUnitPart F hπ x`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitSubringUnit_eq :
    (((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ).symm x).1.1 : F.valuationSubringˣ) *
        (((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
          F hπ).symm x).1.2 : F.valuationSubringˣ) =
      fieldUnitUniformizerUnitPart F hπ x := by
  apply valuationSubringUnitFieldUnitHom_injective
  simp [map_mul, fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitPart_eq_mul_uniformizer_zpow_neg, valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart]

/--
Establishes the identity `((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F
hπ).symm x).1 = (valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm
(fieldUnitUniformizerUnitPart F hπ x)`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_fst_eq_unitPart :
    ((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ).symm x).1 =
      (valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm
        (fieldUnitUniformizerUnitPart F hπ x) := by
  apply (valuationSubringUnitsEquivRootsTimesPrincipalUnits
    F).injective
  simpa
    using
      fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitSubringUnit_eq
        F hπ x

end

section

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) {π : F.valuationSubring}
    (hπ : F.valuation.IsUniformizer (π : K))

/-- Equality of range-restricted values forces equality of the integral
uniformizer exponents. -/
theorem uniformizerValueExponent_eq_of_mrangeRestrict_eq
    {x y : Kˣ}
    (hxy :
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (y : K) = (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (x : K)) :
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ y =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x := by
  apply ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj F) hπ).1
  calc
    _ =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) y := by
      rw [(_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
    _ = (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x := by
      simpa [CompleteDVF.fieldUnitValueUnit] using (congrArg Subtype.val hxy)
    _ = (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^ (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x := by
      rw [(_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]

/-- The uniformizer exponent is locally constant for the range-restricted
valuation topology. -/
theorem eventually_uniformizerValueExponent_eq_mrangeRestrict
    (x : Kˣ) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    ∀ᶠ y : Kˣ in 𝓝 x,
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ y =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x := by
  let Γ :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let := (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have hlocK :
      { y : K |
          Valued.v y =
            Valued.v (x : K)} ∈ 𝓝 (x : K) :=
    by
      have hxrestrictne :=
        ne_of_gt
          ((_root_.Valuation.restrict_pos_iff
            Valued.v (x : K)).2
              (zero_lt_iff.mpr (((_root_.Valuation.ne_zero_iff
                Valued.v).2 x.ne_zero))))
      simpa using
        (Valued.isOpen_sphere K hxrestrictne).mem_nhds (rfl)
  have hlocUnits :
      { y : Kˣ |
          Valued.v (y : K) =
            Valued.v (x : K)} ∈ 𝓝 x := by
    simpa [Set.preimage] using Units.continuous_val.continuousAt hlocK
  exact Filter.mem_of_superset hlocUnits fun y hy =>
    uniformizerValueExponent_eq_of_mrangeRestrict_eq
      F hπ (by
        assumption)

/-- The integer-valued uniformizer exponent is continuous for the
range-restricted valuation topology. -/
theorem continuous_uniformizerValueExponent_mrangeRestrict :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun x : Kˣ => (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x) := by
  let := (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  rw [continuous_iff_continuousAt]
  intro x
  rw [continuousAt_def]
  intro s hs
  exact
    Filter.mem_of_superset
      (eventually_uniformizerValueExponent_eq_mrangeRestrict
        F hπ x)
      (fun y hy => by
        simp_all)

end

section

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The integer factor of the inverse decomposition map is continuous. -/
theorem continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_snd_mrangeRestrict [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun x : Kˣ =>
      ((fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ).symm x).2) := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  exact (continuous_of_discreteTopology.comp (continuous_uniformizerValueExponent_mrangeRestrict
    F hπ)).congr fun x =>
    (fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_snd
      F hπ x).symm

/-- Removing the uniformizer power from a field unit is continuous as a map
to valuation-ring units. -/
theorem continuous_fieldUnitUniformizerUnitPart_mrangeRestrict
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun x : Kˣ =>
      fieldUnitUniformizerUnitPart F hπ x) := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let ϖ := Units.mk0 (π : K) hπ.ne_zero
  have hpow :
      Continuous (fun n : ℤ => ϖ ^ (-n)) :=
    continuous_of_discreteTopology
  have hfield :=
    continuous_id.mul (hpow.comp (continuous_uniformizerValueExponent_mrangeRestrict
      F hπ))
  rw [Units.continuous_iff]
  constructor
  · refine Continuous.subtype_mk ?_ fun x =>
      (fieldUnitUniformizerUnitPart F hπ x :
        F.valuationSubring).2
    convert (Units.continuous_val.comp hfield) using 1
    funext x
    exact ((coe_valuationSubringUnitFieldUnitHom_apply F (fieldUnitUniformizerUnitPart F hπ x)).symm).trans (congrArg (fun y : Kˣ => (y : K)) (valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart F hπ x))
  · refine Continuous.subtype_mk ?_ fun x =>
      (((fieldUnitUniformizerUnitPart F hπ x)⁻¹ :
          F.valuationSubringˣ) : F.valuationSubring).2
    convert (Units.continuous_val.comp hfield.inv) using 1
    funext x
    rfl

/-- The residue-unit map is locally constant on valuation-ring units. -/
theorem eventually_residueUnitHom_eq_mrangeRestrict
    (u : F.valuationSubringˣ) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    ∀ᶠ y : F.valuationSubringˣ in 𝓝 u,
      residueUnitHom F y =
        residueUnitHom F u := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let Γ :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  have hballK :
      { y : K |
          Valued.v
            (y - ((u : F.valuationSubring) : K)) < (1 : Γ) } ∈
        𝓝 (((u : F.valuationSubring) : K)) := by
    rw [Valued.mem_nhds]
    refine ⟨1, ?_⟩
    intro y hy
    simpa using hy
  have hballUnits :
      { y : F.valuationSubringˣ |
          Valued.v
            (((y : F.valuationSubring) : K) -
              ((u : F.valuationSubring) : K)) < (1 : Γ) } ∈
        𝓝 u := by
    simpa [Set.preimage] using (continuous_subtype_val.comp Units.continuous_val).continuousAt hballK
  exact Filter.mem_of_superset hballUnits fun y hy => by
    exact
      (residueUnitHom_eq_iff_residue_eq F y u).2 ((ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal
         (y : F.valuationSubring)
        (u : F.valuationSubring)).2 ((_root_.Valuation.mem_maximalIdeal_iff K F.valuation).2 (by
          exact hy)))

/--
Establishes the identity `((valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm u).1 =
(residueRootsOfUnityEquivResidueFieldUnits F).symm (residueUnitHom F u)`.
-/
theorem valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_eq_residue [Finite F.residueField]
    (u : F.valuationSubringˣ) :
    ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm u).1 =
      (residueRootsOfUnityEquivResidueFieldUnits F).symm
        (residueUnitHom F u) := by
  let E :=
    valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let R :=
    residueRootsOfUnityEquivResidueFieldUnits F
  apply R.injective
  have hp :=
    (residueUnitHom_eq_one_iff
      F ((E.symm u).2 : F.valuationSubringˣ)).2 (E.symm u).2.property
  have hprod :
      ((E.symm u).1 : F.valuationSubringˣ) *
          ((E.symm u).2 : F.valuationSubringˣ) =
        u := by
    exact E.apply_symm_apply u
  have hres := congrArg (residueUnitHom F) hprod
  rw [R.apply_symm_apply]
  change
    residueUnitHom F
        (((E.symm u).1 : F.valuationSubringˣ)) =
      residueUnitHom F u
  simpa [hp] using hres

/--
Establishes the identity `(((valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm u).2 :
F.valuationSubringˣ) = (((valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm u).1 :
F.valuationSubringˣ)⁻¹ * u`.
-/
theorem valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_eq [Finite F.residueField]
    (u : F.valuationSubringˣ) :
    (((valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm u).2 : F.valuationSubringˣ) =
      (((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).1 : F.valuationSubringˣ)⁻¹ * u := by
  let E :=
    valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  have hprod :
      ((E.symm u).1 : F.valuationSubringˣ) *
          ((E.symm u).2 : F.valuationSubringˣ) =
        u := by
    exact E.apply_symm_apply u
  calc
    ((E.symm u).2 : F.valuationSubringˣ) =
        ((E.symm u).1 : F.valuationSubringˣ)⁻¹ *
          (((E.symm u).1 : F.valuationSubringˣ) *
            ((E.symm u).2 : F.valuationSubringˣ)) := by
      simp
    _ = ((E.symm u).1 : F.valuationSubringˣ)⁻¹ * u := by
      rw [hprod]

/-- The root-of-unity factor of the inverse unit decomposition is locally
constant. -/
theorem eventually_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_eq_mrangeRestrict [Finite F.residueField]
    (u : F.valuationSubringˣ) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    ∀ᶠ y : F.valuationSubringˣ in 𝓝 u,
      ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm y).1 =
        ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
          F).symm u).1 := by
  exact
    (eventually_residueUnitHom_eq_mrangeRestrict
      F u).mono fun y hy => by
      simp_all [valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_eq_residue]

/-- The root-of-unity factor of the inverse unit decomposition is continuous. -/
theorem continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_mrangeRestrict [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).1) := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  rw [continuous_iff_continuousAt]
  intro u
  rw [continuousAt_def]
  intro s hs
  exact
    Filter.mem_of_superset
      (eventually_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_eq_mrangeRestrict
        F u)
      (fun y hy => by
        change
          ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
            F).symm y).1 ∈ s
        rw [hy]
        exact (mem_of_mem_nhds hs))

/-- The inclusion of valuation-ring units into field units is continuous for
the range-restricted valuation topology. -/
theorem continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      valuationSubringUnitFieldUnitHom F u) := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have hsub : Continuous (fun x : F.valuationSubring => (x : K)) :=
    continuous_subtype_val
  rw [Units.continuous_iff]
  constructor
  · fun_prop
  fun_prop

/-- The principal-unit factor of the inverse unit decomposition is continuous
as a valuation-ring unit. -/
theorem continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_coe_mrangeRestrict [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      (((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).2 : F.valuationSubringˣ)) := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let E :=
    valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let rootToField := fun u =>
    valuationSubringUnitFieldUnitHom F
      (((E.symm u).1 : F.valuationSubringˣ))
  let unitToField := fun u =>
    valuationSubringUnitFieldUnitHom F u
  have hpartField :=
    ((continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict
      F).comp (continuous_subtype_val.comp (continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_mrangeRestrict
        F))).inv.mul (continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict
      F)
  rw [Units.continuous_iff]
  constructor
  · refine Continuous.subtype_mk ?_ fun u =>
      (((E.symm u).2 : F.valuationSubringˣ) : F.valuationSubring).2
    convert (Units.continuous_val.comp hpartField) using 1
    ext u
    have hfield :=
      congrArg
        (fun a : F.valuationSubringˣ =>
          ((valuationSubringUnitFieldUnitHom F a : Kˣ) : K))
        (valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_eq
          F u)
    exact hfield
  · have hcoercedInv :
        Continuous (fun u : F.valuationSubringˣ =>
          (((((E.symm u).2 : F.valuationSubringˣ)⁻¹ :
            F.valuationSubringˣ) : F.valuationSubring) : K)) := by
      convert (Units.continuous_val.comp hpartField.inv) using 1
      ext u
      have hsndInv :
          (((E.symm u).2 : F.valuationSubringˣ)⁻¹ : F.valuationSubringˣ) =
            ((((E.symm u).1 : F.valuationSubringˣ)⁻¹ * u)⁻¹ :
              F.valuationSubringˣ) := by
        rw [(valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_eq
          F u)]
      have hfieldInv :=
        congrArg
          (fun a : F.valuationSubringˣ =>
            ((valuationSubringUnitFieldUnitHom F a : Kˣ) : K))
          hsndInv
      change
        (((valuationSubringUnitFieldUnitHom F
          (((E.symm u).2 : F.valuationSubringˣ)))⁻¹ : Kˣ) : K) =
          ((((rootToField u)⁻¹ * unitToField u : Kˣ)⁻¹ : Kˣ) : K)
      simpa [E, rootToField, unitToField, map_mul] using hfieldInv
    exact Continuous.subtype_mk hcoercedInv fun u =>
      ((((E.symm u).2 : F.valuationSubringˣ)⁻¹ :
        F.valuationSubringˣ) : F.valuationSubring).2

/-- The principal-unit factor of the inverse unit decomposition is continuous. -/
theorem continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_mrangeRestrict [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).2) := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  exact
    Continuous.subtype_mk
      (continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_coe_mrangeRestrict
        F)
      (fun u => ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).2.property)

/-- The inverse of the unit-level decomposition `Oˣ ≃ μ × U¹` is continuous. -/
theorem continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_mrangeRestrict [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      (valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u) := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  rw [continuous_iff_continuousAt]
  intro u
  rw [ContinuousAt, nhds_prod_eq]
  intro s hs
  rcases Filter.mem_prod_iff.1 hs with ⟨s₁, hs₁, s₂, hs₂, hsubset⟩
  exact Filter.mem_of_superset (Filter.inter_mem ((continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_mrangeRestrict
    F).tendsto u hs₁) ((continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_mrangeRestrict
    F).tendsto u hs₂)) fun x hx =>
    hsubset ⟨hx.1, hx.2⟩

/-- Topological half of the uniformizer–residue–principal-unit decomposition: for the
range-restricted valuation topology, the product map
`μ × U¹ × ℤ → Kˣ` is continuous.  The inverse-continuity packaging is kept
separate from the algebraic decomposition. -/
theorem continuous_rootsPrincipalUnitUniformizerMulHom_mrangeRestrict [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun z : fieldUnitDecompositionFactors F =>
      rootsPrincipalUnitUniformizerMulHom F
        (Units.mk0 (π : K) hπ.ne_zero) z) := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  dsimp [rootsPrincipalUnitUniformizerMulHom]
  have hζ :
      Continuous fun z : fieldUnitDecompositionFactors F =>
        valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) := (continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict
        F).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
  have hp :
      Continuous fun z : fieldUnitDecompositionFactors F =>
        valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) := (continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict
        F).comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
  have hn :
      Continuous fun z : fieldUnitDecompositionFactors F =>
        (Units.mk0 (π : K) hπ.ne_zero : Kˣ) ^ Multiplicative.toAdd z.2 := by
    exact continuous_of_discreteTopology.comp continuous_snd
  exact (hζ.mul hp).mul hn

end

/-- public continuity statement for the forward map in the
`K^* ≃ μ_{q-1} × U^1 × ℤ` decomposition. -/
theorem continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun z : fieldUnitDecompositionFactors F =>
      fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ z) := by
  apply continuous_rootsPrincipalUnitUniformizerMulHom_mrangeRestrict <;> assumption

/-- The inverse map in the `K^* ≃ μ × U^1 × ℤ` decomposition is continuous. -/
theorem continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun x : Kˣ =>
      (fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ).symm x) := by
  let :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let E :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  have hfstComp :=
    (continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_mrangeRestrict
      F).comp
      (continuous_fieldUnitUniformizerUnitPart_mrangeRestrict
        F hπ)
  have hfst :
      Continuous (fun x : Kˣ => (E.symm x).1) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt]
    have hpoint (y : Kˣ) :
        (E.symm y).1 =
          (valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm
            (fieldUnitUniformizerUnitPart F hπ y) := by
      dsimp only [E]
      exact
        fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_fst_eq_unitPart
          F hπ y
    rw [hpoint x]
    exact Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun y => (hpoint y).symm)
      (hfstComp.tendsto x)
  have hsnd :
      Continuous (fun x : Kˣ => (E.symm x).2) := by
    simpa [E] using
      continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_snd_mrangeRestrict
        F hπ
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, nhds_prod_eq]
  intro s hs
  rcases Filter.mem_prod_iff.1 hs with ⟨s₁, hs₁, s₂, hs₂, hsubset⟩
  exact Filter.mem_of_superset (Filter.inter_mem (hfst.tendsto x hs₁) (hsnd.tendsto x hs₂)) fun y hy =>
    hsubset ⟨hy.1, hy.2⟩

/-- The uniformizer–residue–principal-unit decomposition, topological group-isomorphism form for
the range-restricted valuation topology. -/
noncomputable def fieldUnitsContinuousMulEquivRootsPrincipalUnitsUniformizer_of_completeDVF_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    fieldUnitDecompositionFactors F ≃ₜ* Kˣ := by
  letI : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  exact
    { fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ with
      continuous_toFun :=
        continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_mrangeRestrict
          F hπ
      continuous_invFun :=
        continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_mrangeRestrict
          F hπ }

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
