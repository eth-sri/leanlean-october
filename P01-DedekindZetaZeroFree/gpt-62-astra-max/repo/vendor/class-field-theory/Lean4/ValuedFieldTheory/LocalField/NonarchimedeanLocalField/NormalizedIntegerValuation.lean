module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

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
noncomputable def localIntegerValuation :
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
  apply localCompleteDVF_integerRing_moduleFinite

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
noncomputable def localIntegerValuationSubringEquiv :
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
      rw [localIntegerValuation_apply] at hxmem
      simpa using hxmem
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
  left_inv := fun x => by ext; rfl
  right_inv := fun x => by ext; rfl
  map_mul' := fun x y => by ext; rfl
  map_add' := fun x y => by ext; rfl

/-- The valuation-subring equivalence preserves the underlying element of `K`. -/
@[simp]
theorem localIntegerValuationSubringEquiv_apply_coe
    (x : (localIntegerValuation K).valuationSubring) :
    ((localIntegerValuationSubringEquiv K x :
      (localCompleteDVF K).valuationSubring) : K) = x := rfl

/-- The valuation-subring equivalence preserves membership in the maximal ideal. -/
theorem localIntegerValuationSubringEquiv_mem_maximalIdeal_iff
    (x : (localIntegerValuation K).valuationSubring) :
    localIntegerValuationSubringEquiv K x ∈
        IsLocalRing.maximalIdeal (localCompleteDVF K).valuationSubring ↔
      x ∈ IsLocalRing.maximalIdeal
        (localIntegerValuation K).valuationSubring := by
  simp

/-- The valuation-subring equivalence maps the integer maximal ideal onto the canonical one. -/
@[simp]
theorem localIntegerValuationSubringEquiv_map_maximalIdeal :
    (IsLocalRing.maximalIdeal
        (localIntegerValuation K).valuationSubring).map
      (localIntegerValuationSubringEquiv K :
        (localIntegerValuation K).valuationSubring →+*
          (localCompleteDVF K).valuationSubring) =
      IsLocalRing.maximalIdeal (localCompleteDVF K).valuationSubring := by
  apply IsLocalRing.map_ringEquiv_maximalIdeal

/-- The normalized valuation is a complete discrete valuation. -/
noncomputable instance localIntegerValuation_isCompleteDiscrete :
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
    have :=
      Subgroup.isCyclic_of_le
        (show MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom ≤ ⊤ from le_top)
    exact _root_.Valuation.IsRankOneDiscrete.mk' v
  isAdicComplete := by
    let e := localIntegerValuationSubringEquiv K
    let :=
      (localCompleteDVF K).isAdicComplete
    have hcomplete :
        IsAdicComplete
          ((IsLocalRing.maximalIdeal
            (localCompleteDVF K).valuationSubring).map
              e.symm)
          (localIntegerValuation K).valuationSubring :=
      ValuationTheory.DiscreteValuationField.isAdicComplete_map_ringEquiv
        (I := IsLocalRing.maximalIdeal
          (localCompleteDVF K).valuationSubring) e.symm
    have hmap :
        (IsLocalRing.maximalIdeal
          (localCompleteDVF K).valuationSubring).map
            e.symm =
          IsLocalRing.maximalIdeal
            (localIntegerValuation K).valuationSubring := by
      ext x
      rw [Ideal.mem_map_iff_of_surjective
        e.symm e.symm.surjective]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact
          (localIntegerValuationSubringEquiv_mem_maximalIdeal_iff K
            (e.symm y)).1 (by simpa [e] using hy)
      · intro hx
        refine ⟨e x, ?_, by simp [e]⟩
        exact
          (localIntegerValuationSubringEquiv_mem_maximalIdeal_iff K x).2 hx
    simpa [hmap] using hcomplete

/-- The normalized valuation has the same finite residue field as the
canonical local valuation. -/
noncomputable instance localIntegerValuation_residueFinite :
    Finite
      (IsLocalRing.ResidueField
        (localIntegerValuation K).valuationSubring) := by
  have hfinite : Finite (localCompleteDVF K).residueField := by
    change Finite 𝓀[K]
    infer_instance
  let e := localIntegerValuationSubringEquiv K
  exact Finite.of_equiv (localCompleteDVF K).residueField
    (IsLocalRing.ResidueField.mapEquiv e).symm.toEquiv

end LocalFieldTheory

end
