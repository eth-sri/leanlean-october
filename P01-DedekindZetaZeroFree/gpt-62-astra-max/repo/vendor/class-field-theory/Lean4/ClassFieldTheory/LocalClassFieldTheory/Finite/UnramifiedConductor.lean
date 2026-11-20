module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.GroupTheory.Abelianization.Defs
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Conductors and unramified extensions

For an unramified finite abelian extension, normalized valuation identifies
the norm subgroup and shows that all base-field units are norms. Hence its
conductor ideal is `1`.

Conversely, conductor one identifies the norm quotient order with the residue
degree. Finite local reciprocity and the degree formula then force the
ramification index to be one.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel IsMulCommutative
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

section

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L]

theorem normQuotientFiniteOfIsAbelianGalois [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    Finite (NormQuotient K L) := Finite.of_equiv Gal(L / K)
    ((Abelianization.equivOfComm).trans
      (abelianizationEquivNormQuotient K L)).toEquiv

/-- If every base integer unit is a norm, the actual norm quotient is the
cyclic quotient of the normalized value group by the residue degree.

This value-group comparison uses the separable norm-valuation formula for its
residue degree; no unramifiedness assumption is made here. -/
noncomputable def
    chosenNormQuotientEquivZModResidueFinrank_of_fieldPrincipalUnits_zero_le [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (hU : LocalFieldTheory.fieldPrincipalUnits K 0 ≤ localNormSubgroup K L) :
    NormQuotient K L ≃*
      Multiplicative
        (ZMod
          (@Module.finrank 𝓀[K] 𝓀[L] _ _
            (IsLocalRing.ResidueField.instModule
              (R := 𝒪[K])
              (S := 𝒪[L])))) := by
  let vK := multiplicativeIntegerValuation K
  let vL := multiplicativeIntegerValuation L
  refine (normQuotientEquivOfSubgroupEq K L
      (LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup K L) ?_).trans
    (LocalFieldTheory.DiscreteValuationField.fieldNormQuotientEquivZMod
      K L vK vL
        (@Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule

            ))
        ?_ (Classical.choose_spec (multiplicativeIntegerValuation_exists_uniformizer K)) (Classical.choose_spec (multiplicativeIntegerValuation_exists_uniformizer L)) ?_)
  · exact rfl
  · intro x
    simpa [vK, vL, multiplicativeIntegerValuation] using
      (v_normUnits_eq_residue_finrank_mul_of_isGalois K L x)
  · intro x hx
    have hxval : valuationMap K (Additive.ofMul x) = 0 := by
      change vK.val x = 0 at hx
      simpa [vK, multiplicativeIntegerValuation,
        valuationMap_apply] using hx
    obtain ⟨u, hu⟩ :=
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero K x).2 hxval
    simpa [LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup,
      localNormSubgroup] using (hU (by
        rw [← hu]
        exact ⟨u, by simp, rfl⟩))

end

/-- Finite local reciprocity gives the order of the norm quotient in a finite
abelian extension: it is the field degree. -/
theorem card_normQuotient_eq_finrank_of_isAbelianGalois
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    letI : Finite (NormQuotient K L) :=
      normQuotientFiniteOfIsAbelianGalois K L
    Nat.card (NormQuotient K L) = Module.finrank K L := by
  let :=
    normQuotientFiniteOfIsAbelianGalois K L
  let :=
    Finite.of_equiv Gal(L / K)
      (Abelianization.equivOfComm).toEquiv
  calc
    _ =
        Nat.card (Abelianization Gal(L / K)) :=
      Nat.card_congr (abelianizationEquivNormQuotient K L).toEquiv.symm
    _ = Nat.card Gal(L / K) :=
      Nat.card_congr (Abelianization.equivOfComm
        ).toEquiv.symm
    _ = Module.finrank K L := galoisGroup_card_eq_finrank K L

/-- In an actual finite unramified abelian extension, every base-field
integer unit lies in the field-norm subgroup. -/
theorem fieldPrincipalUnits_zero_le_normSubgroup_of_unramifiedValuation
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    LocalFieldTheory.fieldPrincipalUnits K 0 ≤ localNormSubgroup K L := by
  rw [normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure K L]
  rintro x ⟨u, _hu, rfl⟩
  apply (mem_unramifiedNormSubgroup_iff K (Module.finrank K L) _).2
  rw [valuationMap_apply, v_integerUnitsToFieldUnits]
  exact dvd_zero _

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

/-- An unramified finite abelian extension has conductor exponent zero. -/
theorem localConductorExponent_eq_zero_of_unramifiedValuation
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    localConductorExponent K L = 0 := (localConductorExponent_eq_zero_iff K L).2
    (fieldPrincipalUnits_zero_le_normSubgroup_of_unramifiedValuation K L)

/-- An unramified finite abelian extension has conductor ideal `1`. -/
theorem localConductorIdeal_eq_one_of_unramifiedValuation
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    localConductorIdeal K L = 1 := (localConductorIdeal_eq_one_iff_exponent_eq_zero K L).2
    (localConductorExponent_eq_zero_of_unramifiedValuation K L)

/-- A finite abelian extension whose conductor ideal is `1` is unramified.

The proof compares two computations of the actual norm quotient.  Its order
is the residue degree by the norm-valuation formula and the conductor-one
unit inclusion, while finite local reciprocity gives the field degree.
Cancelling the positive residue degree gives ramification index one. -/
theorem isFiniteUnramifiedValuationExtension_of_localConductorIdeal_eq_one
    (hcond : localConductorIdeal K L = 1) :
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L := by
  let hequiv :=
    chosenNormQuotientEquivZModResidueFinrank_of_fieldPrincipalUnits_zero_le
      K L ((localConductorIdeal_eq_one_iff K L).1 hcond)
  let :=
    normQuotientFiniteOfIsAbelianGalois K L
  have hcardResidue :
      Nat.card (NormQuotient K L) =
        @Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule

            ) := by
    rw [Nat.card_congr hequiv.toEquiv]
    exact Nat.card_zmod
      (@Module.finrank 𝓀[K] 𝓀[L] _ _
        (IsLocalRing.ResidueField.instModule

          ))
  have hfpos :
      0 < @Module.finrank 𝓀[K] 𝓀[L] _ _
        (IsLocalRing.ResidueField.instModule

          ) :=
    Module.finrank_pos
  have hcancel :
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] *
        @Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule

            ) =
          1 * @Module.finrank 𝓀[K] 𝓀[L] _ _
            (IsLocalRing.ResidueField.instModule

              ) := by
    calc
      _ = Module.finrank K L := (by
        rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Ring.ne_bot_of_isMaximal_of_not_isField
          (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
          (IsDiscreteValuationRing.not_isField 𝒪[K]))]
        exact (maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure
          K L))
      _ = @Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule

            ) := ((card_normQuotient_eq_finrank_of_isAbelianGalois K L).symm.trans hcardResidue)
      _ = 1 * @Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule

            ) := (one_mul _).symm
  exact ⟨Nat.eq_of_mul_eq_mul_right hfpos hcancel⟩

/-- A finite abelian extension is unramified if and only if its conductor
ideal is `1`. -/
theorem isFiniteUnramifiedValuationExtension_iff_localConductorIdeal_eq_one :
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L ↔
      localConductorIdeal K L = 1 := by
  constructor
  · intro hunramified
    let :=
      hunramified
    exact localConductorIdeal_eq_one_of_unramifiedValuation K L
  · exact isFiniteUnramifiedValuationExtension_of_localConductorIdeal_eq_one K L

/-- A concrete finite abelian local extension is unramified exactly when
its local conductor exponent is zero. -/
theorem isUnramifiedValuedExtension_iff_localConductorExponent_eq_zero :
    IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L ↔
      localConductorExponent K L = 0 :=
  (isFiniteUnramifiedValuationExtension_iff_localConductorIdeal_eq_one
      K L).trans
    (localConductorIdeal_eq_one_iff_exponent_eq_zero K L)

end LocalClassFieldTheory

end
