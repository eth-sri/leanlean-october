module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition
public import ValuedFieldTheory.LocalField.GroupTheory.PowerIndex

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Power-index computations for complete discrete valuation fields

This LubinTate consumer specializes the public commutative-group power-index
API to the unit and principal-unit decompositions of a complete discrete
valuation field.
-/

noncomputable section

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory

namespace LocalFieldTheory.DiscreteValuationField

section CompleteDVF

universe u v

variable {K : Type u} [Field K]

/-- The Teichmüller root factor is finite because it is equivalent to the
unit group of the finite residue field. -/
noncomputable instance finite_residueRootsOfUnityGroup
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    Finite
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :=
  Finite.of_equiv F.residueFieldˣ
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits
      F).symm.toEquiv

/-- A nonzero power has only finitely many roots in the valuation-ring unit
group, by injectivity of `O_Kˣ → Kˣ`. -/
noncomputable instance finite_valuationSubringUnits_nthPowerKernel
    (F : CompleteDVF.{u, v} K) (n : ℕ) [NeZero n] :
    Finite ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) := by
  apply LocalFieldTheory.finite_nthPowerKernel_of_injective F.valuationSubringˣ Kˣ n
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F)
  intro a b hab
  apply Units.ext
  apply Subtype.ext
  simpa only [CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply] using
    congrArg (fun z : Kˣ => (z : K)) hab

/-- A nonzero power has finite kernel on the first principal-unit subgroup. -/
noncomputable instance finite_principalUnits_nthPowerKernel
    (F : CompleteDVF.{u, v} K) (n : ℕ) [NeZero n] :
    Finite
      ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) := by
  apply LocalFieldTheory.finite_nthPowerKernel_of_injective
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)
    F.valuationSubringˣ n
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1).subtype
  exact Subtype.val_injective

/-- Finiteness of the principal-unit power quotient implies finiteness of
the full valuation-ring unit quotient through the root/principal product
decomposition. -/
noncomputable instance finite_valuationSubringUnits_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ)
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Finite (F.valuationSubringˣ ⧸ (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) := by
  let e :
      F.valuationSubringˣ ≃*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm
  exact LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv
    F.valuationSubringˣ
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)
    n e

/-- Finiteness of the principal-unit power quotient, together with a chosen
uniformizer, explicitly yields finiteness of the full field-unit quotient.
This remains a constructor rather than a global instance so the analytic
finite boundary stays visible to callers. -/
theorem finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := by
  let eField :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃*
        Kˣ :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  let eUnits :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
        F.valuationSubringˣ :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let e :
      Kˣ ≃* F.valuationSubringˣ × Multiplicative ℤ :=
    eField.symm.trans
      (MulEquiv.prodCongr eUnits (MulEquiv.refl (Multiplicative ℤ)))
  exact LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv_units_prod_int
    Kˣ F.valuationSubringˣ e

/-- The local-field power-index formula, first equality: after choosing a
uniformizer, the field-unit `n`-th-power quotient has the unit quotient as a
factor and the uniformizer direction contributes exactly `n`. -/
theorem card_fieldUnits_nthPowerQuotient_eq_mul_unit_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite (F.valuationSubringˣ ⧸ (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range)] :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) := by
  let eField :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃*
        Kˣ :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  let eUnits :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
        F.valuationSubringˣ :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let e :
      Kˣ ≃* F.valuationSubringˣ × Multiplicative ℤ :=
    eField.symm.trans
      (MulEquiv.prodCongr eUnits (MulEquiv.refl (Multiplicative ℤ)))
  exact
    LocalFieldTheory.card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int
      Kˣ F.valuationSubringˣ (NeZero.ne n) e

/-- The local-field power-index formula, unit-decomposition reduction: the unit
`n`-th-power quotient splits into the residue root-of-unity factor and the
first principal-unit factor. -/
theorem card_unit_nthPowerQuotient_eq_mul_roots_principalUnit_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ)
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ⧸
            (powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).range) *
        Nat.card
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
            (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) := by
  let e :
      F.valuationSubringˣ ≃*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm
  exact
    LocalFieldTheory.card_nthPowerQuotient_eq_mul_of_mulEquiv_prod
      F.valuationSubringˣ
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) n e

/-- On the finite Teichmuller root factor, the `n`-th-power quotient has the
same size as the subgroup killed by `n`. -/
theorem card_residueRoots_nthPowerQuotient_eq_nthPowerKernel
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ) :
    Nat.card
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ⧸
          (powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).range) =
      Nat.card
        ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) := by
  classical
  let e :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ≃*
        F.residueFieldˣ :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits
      F
  have :
      Finite (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :=
    Finite.of_equiv F.residueFieldˣ e.symm.toEquiv
  exact
    LocalFieldTheory.card_nthPowerQuotient_eq_nthPowerKernel
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) n

/-- The `n`-torsion kernel of the full unit group splits into the finite
Teichmuller root factor and the first principal-unit factor. -/
theorem card_unit_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ) [NeZero n] :
    Nat.card
        ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) =
      Nat.card
          ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) *
        Nat.card
          ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) := by
  let e :
      F.valuationSubringˣ ≃*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm
  exact
    LocalFieldTheory.card_nthPowerKernel_eq_mul_of_mulEquiv_prod
      F.valuationSubringˣ
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) n e

/-- For nonzero `n`, the field-unit `n`-torsion kernel is the unit
`n`-torsion kernel; the uniformizer direction has no nontrivial finite
`n`-torsion. -/
theorem card_fieldUnits_nthPowerKernel_eq_unit_nthPowerKernel
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n] :
    Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) =
      Nat.card ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) := by
  let eField :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃*
        Kˣ :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  let eUnits :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
        F.valuationSubringˣ :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let e :
      Kˣ ≃* F.valuationSubringˣ × Multiplicative ℤ :=
    eField.symm.trans
      (MulEquiv.prodCongr eUnits (MulEquiv.refl (Multiplicative ℤ)))
  exact
    LocalFieldTheory.card_nthPowerKernel_eq_of_mulEquiv_units_prod_int
      Kˣ F.valuationSubringˣ (NeZero.ne n) e

/-- For nonzero `n`, the field-unit `n`-torsion kernel is the product of the
Teichmuller `n`-torsion kernel and the first principal-unit `n`-torsion
kernel.  This is the group-theoretic `μ_n(K)` decomposition behind
the local-field power-index formula. -/
theorem card_fieldUnits_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n] :
    Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) =
      Nat.card
          ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) *
        Nat.card
          ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) := by
  rw [card_fieldUnits_nthPowerKernel_eq_unit_nthPowerKernel
    (F := F) hπ n]
  rw [card_unit_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel
    (F := F) n]

/-- The local-field power-index formula, unit-index reduction after identifying the finite
root-of-unity quotient with its `n`-torsion kernel.  The remaining analytic
input is the principal-unit factor, supplied by the field-unit structure theorem. -/
theorem card_unit_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ)
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card
          ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) *
        Nat.card
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
            (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) := by
  rw [card_unit_nthPowerQuotient_eq_mul_roots_principalUnit_nthPowerQuotient,
    card_residueRoots_nthPowerQuotient_eq_nthPowerKernel]

/-- The local-field power-index formula, unit-index form reduced to the analytic principal-unit
input.  If the field-unit structure theorem supplies the principal-unit quotient as its
`n`-torsion kernel times a defect factor `c`, then the same defect multiplies
the full unit `n`-torsion kernel. -/
theorem card_unit_nthPowerQuotient_eq_mul_unitKernel_of_principalUnit_index
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {n c : ℕ} [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (hprincipal :
      Nat.card
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
            (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) =
        Nat.card
          ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) * c) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) * c := by
  rw [card_unit_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient]
  rw [hprincipal]
  rw [card_unit_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel]
  ring







/-- The local-field power-index formula, field-unit index reduced to the finite root factor and the
principal-unit factor.  The uniformizer contributes `n`; the finite
root-of-unity factor is already expressed as its `n`-torsion kernel. -/
theorem card_fieldUnits_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n *
        (Nat.card
            ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) *
          Nat.card
            ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
              (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)) := by
  rw [card_fieldUnits_nthPowerQuotient_eq_mul_unit_nthPowerQuotient
    (F := F) hπ n]
  rw [card_unit_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient
    (F := F) n]





/-- The field-unit structure theorem logarithmic transport, principal-unit form: any
multiplicative logarithm equivalence from `U¹` to an additive group identifies
the principal-unit `n`-th-power quotient with the additive quotient by
`n`-fold multiples. -/
theorem card_principalUnit_nthPowerQuotient_eq_additive_nsmulQuotient_of_logEquiv
    (F : CompleteDVF.{u, v} K)
    (A : Type*) [AddCommGroup A]
    (n : ℕ)
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A) :
    Nat.card
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
          (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) =
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) :=
  LocalFieldTheory.card_nthPowerQuotient_eq_additive_nsmulQuotient_of_mulEquiv
    (A := A) (G := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) n e

/-- The field-unit structure theorem logarithmic transport, kernel form: under the same
principal-unit logarithm equivalence, the principal-unit `n`-torsion kernel
has the same cardinality as the additive kernel of `x ↦ n • x`. -/
theorem card_principalUnit_nthPowerKernel_eq_additive_nsmulKernel_of_logEquiv
    (F : CompleteDVF.{u, v} K)
    (A : Type*) [AddCommGroup A]
    (n : ℕ) [NeZero n]
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A) :
    Nat.card ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) =
      Nat.card (LocalFieldTheory.nsmulAddKernel A n) :=
  LocalFieldTheory.card_nthPowerKernel_eq_additive_nsmulKernel_of_mulEquiv
    (A := A) (G := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) n e



/-- The field-unit structure theorem logarithmic transport in kernel-factor form: after a
principal-unit logarithm equivalence, a finite additive kernel/cokernel
calculation immediately supplies the kernel times defect factor used by
the local-field power-index formula. -/
theorem card_principalUnit_nthPowerQuotient_eq_mul_kernel_of_logEquiv
    (F : CompleteDVF.{u, v} K)
    (A : Type*) [AddCommGroup A]
    (n c : ℕ) [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A)
    (hadd :
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) =
        Nat.card (LocalFieldTheory.nsmulAddKernel A n) * c) :
    Nat.card
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
          (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) =
      Nat.card ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) * c := by
  rw [card_principalUnit_nthPowerQuotient_eq_additive_nsmulQuotient_of_logEquiv
    (F := F) (A := A) n e]
  rw [hadd]
  rw [card_principalUnit_nthPowerKernel_eq_additive_nsmulKernel_of_logEquiv
    (F := F) (A := A) n e]







/-- The local-field power-index formula, unit-index form fed directly by a principal-unit logarithm
equivalence and an additive kernel/cokernel calculation. -/
theorem card_unit_nthPowerQuotient_eq_mul_unitKernel_of_logEquiv
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    (A : Type*) [AddCommGroup A]
    {n c : ℕ} [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A)
    (hadd :
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) =
        Nat.card (LocalFieldTheory.nsmulAddKernel A n) * c) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) * c :=
  card_unit_nthPowerQuotient_eq_mul_unitKernel_of_principalUnit_index
    (F := F)
    (hprincipal :=
      card_principalUnit_nthPowerQuotient_eq_mul_kernel_of_logEquiv
        (F := F) (A := A) n c e hadd)



/-- The local-field power-index formula reduced to the analytic principal-unit index statement.
If the field-unit structure theorem supplies the principal-unit quotient as its `n`-torsion
kernel times a defect factor `c`, then the field-unit quotient is `n` times
the field-unit `n`-torsion kernel times the same defect. -/
theorem card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_principalUnit_index
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {n c : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (hprincipal :
      Nat.card
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
            (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) =
        Nat.card
          ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) * c) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) * c) := by
  rw [card_fieldUnits_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient
    (F := F) hπ n]
  rw [hprincipal]
  rw [card_fieldUnits_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel
    (F := F) hπ n]
  ring

/-- The local-field power-index formula, field-index form fed directly by a principal-unit logarithm
equivalence and an additive kernel/cokernel calculation. -/
theorem card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_logEquiv
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (A : Type*) [AddCommGroup A]
    {n c : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A)
    (hadd :
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) =
        Nat.card (LocalFieldTheory.nsmulAddKernel A n) * c) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) * c) :=
  card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_principalUnit_index
    (F := F) hπ
    (hprincipal :=
      card_principalUnit_nthPowerQuotient_eq_mul_kernel_of_logEquiv
        (F := F) (A := A) n c e hadd)







end CompleteDVF

end LocalFieldTheory.DiscreteValuationField

end
