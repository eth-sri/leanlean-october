module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The normalized integer valuation of a local field

The Kummer branch of the local existence theorem uses power-class index
formulas stated for valuations with value group
`WithZero (Multiplicative ℤ)`.  A nonarchimedean local field carries its
canonical valuation in an intrinsic value group.  This file transports that
valuation to the integer model and proves that completeness and the finite
residue field are preserved.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical local valuation, normalized to the value group
`WithZero (Multiplicative ℤ)`. -/
def localIntegerValuation :
    _root_.Valuation K (WithZero (Multiplicative ℤ)) :=
  _root_.Valuation.map
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
    (ValuativeRel.valuation K)

/-- The integer-valued valuation applies the canonical value-group isomorphism. -/
@[simp]
theorem localIntegerValuation_apply (x : K) :
    localIntegerValuation K x =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (ValuativeRel.valuation K x) :=
  rfl

/-- The valuation in the canonical complete-DVF package is the original local valuation. -/
theorem localCompleteDVF_valuation_eq :
    (localCompleteDVF K).valuation = ValuativeRel.valuation K := by
  rfl

/-- A finite separable local extension is finite over the actual canonical
valuation integer ring.  This transports the finite-module theorem for the
complete-DVF packages along the equality of their valuations. -/
theorem integerRing_moduleFinite_of_finite_separable
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    Module.Finite
      (ValuativeRel.valuation K).integer
      (ValuativeRel.valuation L).integer := by
  let :
      (localCompleteDVF K).valuation.HasExtension
        (localCompleteDVF L).valuation :=
    localCompleteDVFValuation_hasExtension K L
  let :
      IsScalarTower (localCompleteDVF K).valuationSubring
        (localCompleteDVF L).valuationSubring L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let :
      Module.Finite (localCompleteDVF K).valuationSubring
        (localCompleteDVF L).valuationSubring :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
      (localCompleteDVF K) (localCompleteDVF L)
  have hK :
      (ValuativeRel.valuation K).integer =
        ((localCompleteDVF K).valuation.valuationSubring).toSubring := by
    rfl
  have hL :
      (ValuativeRel.valuation L).integer =
        ((localCompleteDVF L).valuation.valuationSubring).toSubring := by
    rfl
  let eK :
      (localCompleteDVF K).valuationSubring ≃+*
        (ValuativeRel.valuation K).integer :=
    RingEquiv.subringCongr hK.symm
  let eL :
      (localCompleteDVF L).valuationSubring ≃+*
        (ValuativeRel.valuation L).integer :=
    RingEquiv.subringCongr hL.symm
  refine Module.Finite.of_equiv_equiv eK eL ?_
  rfl

/-- The normalized integer valuation is onto. -/
theorem localIntegerValuation_surjective :
    Function.Surjective (localIntegerValuation K) := by
  intro gamma
  obtain ⟨x, hx⟩ :=
    ValuativeRel.valuation_surjective
      ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm gamma)
  refine ⟨x, ?_⟩
  simp [localIntegerValuation, hx]

/-- Identity on field elements gives the valuation-ring equivalence attached
to the normalization of the value group. -/
def localIntegerValuationSubringEquiv :
    (localIntegerValuation K).valuationSubring ≃+*
      (localCompleteDVF K).valuationSubring where
  toFun := fun x => ⟨x, by
    change (localCompleteDVF K).valuation (x : K) ≤ 1
    rw [localCompleteDVF_valuation_eq]
    have hx :
        IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
            (ValuativeRel.valuation K (x : K)) ≤
          IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K 1 := by
      have hxmem := x.property
      change localIntegerValuation K (x : K) ≤ 1 at hxmem
      simp_all
    exact
      (map_le_map_iff
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).mp hx⟩
  invFun := fun x => ⟨x, by
    have hx : ValuativeRel.valuation K (x : K) ≤ 1 := by
      have hxmem := x.property
      change (localCompleteDVF K).valuation (x : K) ≤ 1 at hxmem
      rw [localCompleteDVF_valuation_eq] at hxmem
      exact hxmem
    change
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K (x : K)) ≤ 1
    simpa only [localIntegerValuation, _root_.Valuation.map_apply,
      map_one] using
      (map_le_map_iff
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).mpr hx⟩
  left_inv := fun x => by rfl
  right_inv := fun x => by rfl
  map_mul' := fun x y => by rfl
  map_add' := fun x y => by rfl

/-- The valuation-subring equivalence preserves membership in the maximal ideal. -/
theorem localIntegerValuationSubringEquiv_mem_maximalIdeal_iff
    (x : (localIntegerValuation K).valuationSubring) :
    localIntegerValuationSubringEquiv K x ∈
        IsLocalRing.maximalIdeal (localCompleteDVF K).valuationSubring ↔
      x ∈ IsLocalRing.maximalIdeal
        (localIntegerValuation K).valuationSubring := by
  simp

/-- The normalized valuation is a complete discrete valuation. -/
instance localIntegerValuation_isCompleteDiscrete :
    ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (localIntegerValuation K) where
  isRankOneDiscrete := by
    let v := localIntegerValuation K
    have : v.IsNontrivial := by
      obtain ⟨x, hx⟩ :=
        localIntegerValuation_surjective K (WithZero.exp (-1 : ℤ))
      refine ⟨⟨x, ?_, ?_⟩⟩
      · rw [hx]
        simp
      · rw [hx]
        simp
    have : IsCyclic (MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom) :=
      Subgroup.isCyclic_of_le
        (show MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom ≤ ⊤ from le_top)
    exact _root_.Valuation.IsRankOneDiscrete.mk' v
  isAdicComplete := by
    let e := localIntegerValuationSubringEquiv K
    let : IsAdicComplete
        (IsLocalRing.maximalIdeal (localCompleteDVF K).valuationSubring)
        (localCompleteDVF K).valuationSubring :=
      (localCompleteDVF K).isAdicComplete
    have hcomplete :
        IsAdicComplete
          ((IsLocalRing.maximalIdeal
            (localCompleteDVF K).valuationSubring).map
              (e.symm : (localCompleteDVF K).valuationSubring →+*
                (localIntegerValuation K).valuationSubring))
          (localIntegerValuation K).valuationSubring :=
      ValuationTheory.DiscreteValuationField.isAdicComplete_map_ringEquiv
        (I := IsLocalRing.maximalIdeal
          (localCompleteDVF K).valuationSubring) e.symm
    have hmap :
        (IsLocalRing.maximalIdeal
          (localCompleteDVF K).valuationSubring).map
            (e.symm : (localCompleteDVF K).valuationSubring →+*
              (localIntegerValuation K).valuationSubring) =
          IsLocalRing.maximalIdeal
            (localIntegerValuation K).valuationSubring := by
      ext x
      rw [Ideal.mem_map_iff_of_surjective
        (e.symm : (localCompleteDVF K).valuationSubring →+*
          (localIntegerValuation K).valuationSubring) e.symm.surjective]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp_all
      · intro hx
        refine ⟨e x, ?_, by simp [e]⟩
        simp_all
    simpa [hmap] using hcomplete

/-- The normalized valuation has the same finite residue field as the
canonical local valuation. -/
instance localIntegerValuation_residueFinite :
    Finite
      (IsLocalRing.ResidueField
        (localIntegerValuation K).valuationSubring) := by
  have hfinite : Finite (localCompleteDVF K).residueField := by
    change Finite 𝓀[K]
    infer_instance
  let e := localIntegerValuationSubringEquiv K
  exact Finite.of_equiv (localCompleteDVF K).residueField
    (IsLocalRing.ResidueField.mapEquiv e).symm.toEquiv
