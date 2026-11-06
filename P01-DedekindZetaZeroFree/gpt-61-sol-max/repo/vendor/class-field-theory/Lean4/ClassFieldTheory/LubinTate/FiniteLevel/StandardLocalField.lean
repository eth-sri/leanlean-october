module

public import Mathlib

public import ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerDecomposition
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# The canonical local-field package for Lubin--Tate applications

A topology-first nonarchimedean local field carries the canonical valuation
used by finite local reciprocity.  This file packages that valuation as a
`LocalField` and identifies its valuation ring and principal-unit filtration
with the pre-existing `𝒪[K]`, `principalUnits`, and `LocalFieldTheory.fieldPrincipalUnits`
interfaces.
-/

noncomputable section

open scoped ValuativeRel

namespace LubinTate

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical complete discrete valuation on `K`, together with its
finite residue field, packaged for the standard Lubin--Tate construction. -/
noncomputable def standardLocalField : LocalField K where
  toCompleteDVF := LocalFieldTheory.localCompleteDVF K
  residueFinite := by
    change Finite 𝓀[K]
    infer_instance

/-- Forgetting residue-field finiteness recovers the canonical complete-DVF
package used by finite local reciprocity. -/
@[simp]
theorem standardLocalField_toCompleteDVF :
    (standardLocalField K).toCompleteDVF =
      LocalFieldTheory.localCompleteDVF K :=
  rfl

/-- The valuation in the canonical local-field package is the valuation
attached to the given valuative relation. -/
theorem standardLocalField_valuation_eq :
    (standardLocalField K).valuation =
      ValuativeRel.valuation K := by
  unfold standardLocalField
  unfold LocalFieldTheory.localCompleteDVF
  unfold ValuationTheory.Valuations.completeDVFOfCompleteValuedField
  rfl

/-- The residue field in the canonical package has the same finite
cardinality as the topology-first residue field. -/
@[simp]
theorem standardLocalField_residueField_natCard :
    Nat.card (standardLocalField K).residueField =
      Nat.card 𝓀[K] :=
  rfl

/-- Identity on underlying field elements identifies the topology-first
integer ring with the valuation ring of the canonical package. -/
noncomputable def standardLocalFieldIntegerEquiv :
    𝒪[K] ≃+* (standardLocalField K).valuationSubring where
  toFun x := ⟨x, by
    change (standardLocalField K).valuation (x : K) ≤ 1
    rw [standardLocalField_valuation_eq]
    exact x.property⟩
  invFun x := ⟨x, by
    change ValuativeRel.valuation K (x : K) ≤ 1
    rw [← standardLocalField_valuation_eq]
    exact x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl

/-- The canonical integer-ring equivalence preserves the underlying field
element. -/
@[simp]
theorem standardLocalFieldIntegerEquiv_apply_coe (x : 𝒪[K]) :
    (((standardLocalFieldIntegerEquiv K x)) : K) =
      (x : K) :=
  rfl

/-- The inverse canonical integer-ring equivalence preserves the underlying
field element. -/
@[simp]
theorem standardLocalFieldIntegerEquiv_symm_apply_coe
    (x : (standardLocalField K).valuationSubring) :
    ((((standardLocalFieldIntegerEquiv K).symm x)) : K) =
      (x : K) :=
  rfl













































/-- The induced multiplicative equivalence between the two valuation-ring
unit groups. -/
noncomputable def standardLocalFieldIntegerUnitsEquiv  :=
  Units.mapEquiv
    (standardLocalFieldIntegerEquiv K).toMulEquiv

/-- The induced unit equivalence preserves the underlying field element. -/
@[simp]
theorem standardLocalFieldIntegerUnitsEquiv_apply_coe (u : 𝒪[K]ˣ) :
    ((((standardLocalFieldIntegerUnitsEquiv K u) :
        (standardLocalField K).valuationSubring)) : K) =
      ((u : 𝒪[K]) : K) :=
  rfl

/-- Under the canonical unit equivalence, packaged higher principal units
are exactly the topology-first principal units. -/
theorem
    standardLocalFieldIntegerUnitsEquiv_mem_higherPrincipalUnitGroup_iff
    (n : ℕ) (u : 𝒪[K]ˣ) :
    standardLocalFieldIntegerUnitsEquiv K u ∈
        higherPrincipalUnitGroup
          (standardLocalField K).toCompleteDVF n ↔
      u ∈ principalUnits K n := by
  rfl

/-- Mapping packaged higher principal units back through the canonical
integer-unit equivalence gives the topology-first principal-unit subgroup. -/
theorem standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnits
    (n : ℕ) :
    (higherPrincipalUnitGroup
        (standardLocalField K).toCompleteDVF n).map
        (standardLocalFieldIntegerUnitsEquiv K).symm.toMonoidHom =
      principalUnits K n := by
  let e := standardLocalFieldIntegerUnitsEquiv K
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    change a ∈
      higherPrincipalUnitGroup
        (standardLocalField K).toCompleteDVF n at ha
    exact
      (standardLocalFieldIntegerUnitsEquiv_mem_higherPrincipalUnitGroup_iff
        K n (e.symm a)).1
        (ha)
  · intro hu
    have heu :
        e u ∈ higherPrincipalUnitGroup
          (standardLocalField K).toCompleteDVF n :=
      (standardLocalFieldIntegerUnitsEquiv_mem_higherPrincipalUnitGroup_iff
        K n u).2 hu
    exact ⟨e u, heu, e.symm_apply_apply u⟩

/-- Inclusion of packaged valuation-ring units into field units, expressed
through the canonical integer-ring identification. -/
noncomputable def standardLocalFieldValuationUnitsToFieldUnits  :=
  (integerUnitsToFieldUnits K).comp
    (standardLocalFieldIntegerUnitsEquiv K).symm.toMonoidHom

/-- The packaged valuation-unit inclusion preserves the underlying field
element. -/
@[simp]
theorem standardLocalFieldValuationUnitsToFieldUnits_apply_coe
    (u : (standardLocalField K).valuationSubringˣ) :
    ((standardLocalFieldValuationUnitsToFieldUnits K u) : K) =
      ((u :
        (standardLocalField K).valuationSubring) : K) :=
  rfl

/-- The packaged higher principal-unit subgroup maps exactly to the
topology-first field principal-unit subgroup. -/
theorem standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnits
    (n : ℕ) :
    (higherPrincipalUnitGroup
        (standardLocalField K).toCompleteDVF n).map
        (standardLocalFieldValuationUnitsToFieldUnits K) =
      LocalFieldTheory.fieldPrincipalUnits K n := by
  rfl






















/-- The canonical chosen uniformizer of `𝒪[K]`, transported to the
valuation ring of the standard local-field package. -/
noncomputable def standardLocalFieldUniformizer  :=
  standardLocalFieldIntegerEquiv K
    (chosenIntegerRingUniformizer K)

/-- The transported canonical uniformizer has the expected underlying field
element. -/
@[simp]
theorem standardLocalFieldUniformizer_coe :
    ((standardLocalFieldUniformizer K) : K) =
      ((chosenIntegerRingUniformizer K) : K) :=
  rfl

/-- The transported canonical prime element is a uniformizer for the
valuation in the standard local-field package. -/
theorem standardLocalFieldUniformizer_isUniformizer :
    (standardLocalField K).valuation.IsUniformizer
      (standardLocalFieldUniformizer K : K) := by
  have hirr :
      Irreducible (standardLocalFieldUniformizer K) :=
    (chosenIntegerRingUniformizer_irreducible K).map
      (standardLocalFieldIntegerEquiv K)
  exact
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := (standardLocalField K).valuation)
      hirr.maximalIdeal_eq

end LubinTate

end
