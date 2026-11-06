module

public import Mathlib

public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
public import Mathlib.RingTheory.AdicCompletion.Topology

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Range restriction for complete discretely valued fields

This file specializes multiplicative-range restriction to `CompleteDVF` and
transports residue finiteness, adic completeness, cyclicity, and discreteness.
-/

noncomputable section

universe u v

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

section
variable (F : CompleteDVF.{u, v} K)
include F
/-- Restrict the chosen valuation of a complete DVF to its actual
multiplicative range.  This keeps the valuation ring, maximal ideal, and
residue field unchanged while eliminating irrelevant ambient value-group
elements. -/
def mrangeRestrict    :=
  WithZeroValuation.mrangeRestrict F.valuation

/--
The defining evaluation formula for `mrangeRestrict` is `((CompleteDVF.mrangeRestrict F) x :
F.ValueGroup) = F.valuation x`.
-/
@[simp]
theorem mrangeRestrict_apply   (x : K) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) x : F.ValueGroup) = F.valuation x :=
  rfl

/-- The residue field remains finite after restricting the value group to the
actual multiplicative range. -/
def mrangeRestrict_residueField_finite
      [Finite F.residueField]  :=
  Finite.of_equiv F.residueField
    (WithZeroValuation.residueFieldEquivMrangeRestrict
      F.valuation).toEquiv

/-- The range-restricted valuation ring is adically complete because it is
identified with the original complete-DVF valuation ring and the maximal ideal
is preserved by that identification. -/
theorem mrangeRestrict_isAdicComplete
      :
    IsAdicComplete
      (IsLocalRing.maximalIdeal (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring := by
  let e : F.valuationSubring ≃+* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    WithZeroValuation.valuationSubringEquivMrangeRestrict
      F.valuation
  let  :=
    e.toRingHom.toAlgebra
  let eLin :
      F.valuationSubring ≃ₗ[F.valuationSubring]
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        (intros; abel) }
  have hcompleteBase  :=
    F.isAdicComplete
  assumption

/-- The actual multiplicative range of a complete-DVF valuation is generated
by the image of a discrete valuation generator. -/
theorem mrangeRestrict_units_isCyclic
      :
    IsCyclic (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ := by
  let γ  :=
    _root_.Valuation.IsRankOneDiscrete.generator F.valuation
  have hγrange : (γ : F.ValueGroup) ∈ Set.range F.valuation :=
    _root_.Valuation.IsRankOneDiscrete.generator_mem_range K F.valuation
  let γm : MonoidHom.mrange F.valuation.toMonoidWithZeroHom :=
    ⟨(γ : F.ValueGroup), hγrange⟩
  have hγm_ne : γm ≠ 0 := by
    intro hzero
    have hγzero : (γ : F.ValueGroup) = 0 := congrArg
          (fun z : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom => (z : F.ValueGroup))
          hzero
    exact Units.ne_zero γ hγzero
  let δ : (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ :=
    Units.mk0 γm hγm_ne
  have htop : Subgroup.zpowers δ = ⊤ := by
    rw [eq_top_iff]
    intro η _
    have hη_ne : ((η : MonoidHom.mrange
        F.valuation.toMonoidWithZeroHom) : F.ValueGroup) ≠ 0 := by
      intro hzero
      have hηzero :
          (η : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom) = 0 := by
        ext
        exact hzero
      exact Units.ne_zero η hηzero
    obtain ⟨x, hx⟩ :=
      MonoidHom.mem_mrange.mp
        ((η : MonoidHom.mrange
          F.valuation.toMonoidWithZeroHom).2)
    let ηΓ  :=
      Units.mk0
        (((η : MonoidHom.mrange
          F.valuation.toMonoidWithZeroHom) : F.ValueGroup))
        hη_ne
    have hηΓ_mem :
        ηΓ ∈ MonoidWithZeroHom.valueGroup
          (MonoidWithZeroHom.ofClass F.valuation) :=
      MonoidWithZeroHom.mem_valueGroup
        (MonoidWithZeroHom.ofClass F.valuation) ⟨x, hx⟩
    rw [_root_.Valuation.ofClass_eq_toMonoidWithZeroHom] at hηΓ_mem
    rw [← _root_.Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup
      F.valuation, Subgroup.mem_zpowers_iff] at hηΓ_mem
    rcases hηΓ_mem with ⟨z, hz⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨z, ?_⟩
    let φ  :=
      Units.map (MonoidHom.mrange F.valuation.toMonoidWithZeroHom).subtype
    have hsub_inj :
        Function.Injective
          ((MonoidHom.mrange F.valuation.toMonoidWithZeroHom).subtype) := by
      intro a b h
      exact Subtype.ext h
    have hφinj : Function.Injective φ :=
      Units.map_injective hsub_inj
    have hφδ : φ δ = γ := by
      apply Units.ext
      rfl
    have hφη : φ η = ηΓ := by
      apply Units.ext
      rfl
    apply hφinj
    calc
      φ (δ ^ z) = φ δ ^ z := map_zpow φ δ z
      _ = γ ^ z := by rw [hφδ]
      _ = ηΓ := hz
      _ = φ η := hφη.symm
  exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨δ, htop⟩

/-- The range-restricted valuation is nontrivial whenever the original
complete-DVF valuation is nontrivial. -/
theorem mrangeRestrict_isNontrivial
      :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsNontrivial := by
  rcases _root_.Valuation.IsNontrivial.exists_val_nontrivial
      (v := F.valuation) with ⟨x, hx0, hx1⟩
  refine ⟨⟨x, ?_, ?_⟩⟩
  · intro hx
    exact hx0 (by
      have h :=
        congrArg
          (fun z : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom => (z : F.ValueGroup)) hx
      exact h)
  · intro hx
    exact hx1 (by
      have h :=
        congrArg
          (fun z : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom => (z : F.ValueGroup)) hx
      exact h)

/-- Restricting a complete-DVF valuation to its actual multiplicative range
preserves rank-one discreteness. -/
theorem mrangeRestrict_isRankOneDiscrete
      :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsRankOneDiscrete := by
  have  :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  have  :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isNontrivial F)
  have  :=
    Subgroup.isCyclic_of_le (show
      MonoidWithZeroHom.valueGroup
        (MonoidWithZeroHom.ofClass
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)) ≤
          ⊤ from le_top)
  infer_instance

/-- The range-restricted valuation is rank one as a valuation into its actual
value group. -/
@[implicit_reducible]
noncomputable def mrangeRestrict_rankOne
      :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).RankOne := by
  haveI  :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isNontrivial F)
  haveI  :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  exact WithZeroValuation.rankOneOfUnitsIsCyclic (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)
end


end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
