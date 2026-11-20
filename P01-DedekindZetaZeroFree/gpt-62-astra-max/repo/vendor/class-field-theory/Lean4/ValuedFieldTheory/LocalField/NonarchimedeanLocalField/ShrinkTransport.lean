module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Small
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Topology.Instances.Shrink

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Transporting local-field structures to a small representative

This file records the valuation and topology on the `Type 0` representative
of an arbitrary-universe nonarchimedean local field.
-/

noncomputable section

namespace LocalFieldTheory

open ValuativeRel Filter
open scoped Topology

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

 alias smallLocalField := nonarchimedeanLocalField_small

/-- The canonical valuation pulled back to the small carrier. -/
noncomputable def shrinkLocalFieldValuation :
    letI : Small.{0} K := smallLocalField K
    Valuation (Shrink.{0} K) (ValueGroupWithZero K) := by
  letI : Small.{0} K := smallLocalField K
  exact (valuation K).comap (Shrink.ringEquiv K).toRingHom

/-- The valuative relation on the small carrier, transported from `K`. -/
@[instance_reducible]
noncomputable def shrinkLocalFieldValuativeRel :
    letI : Small.{0} K := smallLocalField K
    ValuativeRel (Shrink.{0} K) := by
  letI : Small.{0} K := smallLocalField K
  exact ValuativeRel.ofValuation (shrinkLocalFieldValuation K)

/-- The small carrier inherits local compactness from `K`. -/
theorem shrinkLocalField_locallyCompact :
    letI : Small.{0} K := smallLocalField K
    LocallyCompactSpace (Shrink.{0} K) := by
  let := smallLocalField K
  exact (Shrink.homeomorph K).symm.isOpenEmbedding.locallyCompactSpace

/-- The pulled-back valuative relation is nontrivial. -/
theorem shrinkLocalField_isNontrivial :
    letI : Small.{0} K := smallLocalField K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ValuativeRel.IsNontrivial (Shrink.{0} K) := by
  let := smallLocalField K
  let := shrinkLocalFieldValuativeRel K
  let v := shrinkLocalFieldValuation K
  let := Valuation.Compatible.ofValuation v
  refine (ValuativeRel.isNontrivial_iff_isNontrivial v).2 ?_
  obtain ⟨x, hx0, hx1⟩ := ((ValuativeRel.isNontrivial_iff_isNontrivial (valuation K)).mp inferInstance).exists_val_nontrivial
  refine ⟨(Shrink.ringEquiv K).symm x, ?_, ?_⟩
  · simpa using hx0
  · simp_all [v, shrinkLocalFieldValuation]

/-- Strict valuation comparisons are preserved by the small-carrier ring
equivalence. -/
theorem shrinkLocalField_valuation_lt_iff :
    letI : Small.{0} K := smallLocalField K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ∀ x y : Shrink.{0} K,
      valuation (Shrink.{0} K) x < valuation (Shrink.{0} K) y ↔
        valuation K (Shrink.ringEquiv K x) <
          valuation K (Shrink.ringEquiv K y) := by
  let := smallLocalField K
  let := shrinkLocalFieldValuativeRel K
  intro x y
  let v := shrinkLocalFieldValuation K
  let := Valuation.Compatible.ofValuation v
  calc
    _ < valuation (Shrink.{0} K) y
        ↔ x <ᵥ y := (valuation (Shrink.{0} K)).vlt_iff_lt.symm
    _ ↔ v x < v y := v.vlt_iff_lt
    _ ↔ valuation K (Shrink.ringEquiv K x) <
        valuation K (Shrink.ringEquiv K y) := by
          rfl

/-- The transported topology is compatible with the transported additive
group structure. -/
theorem shrinkLocalField_isTopologicalAddGroup :
    letI : Small.{0} K := smallLocalField K
    IsTopologicalAddGroup (Shrink.{0} K) := by
  let := smallLocalField K
  exact isTopologicalAddGroup_induced (Shrink.ringEquiv K).toAddMonoidHom

/-- The transported topology is the valuative topology of the pulled-back
valuation. -/
theorem shrinkLocalField_isValuativeTopology :
    letI : Small.{0} K := smallLocalField K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    IsValuativeTopology (Shrink.{0} K) := by
  let := smallLocalField K
  let := shrinkLocalFieldValuativeRel K
  let :=
    shrinkLocalField_isTopologicalAddGroup K
  let e := Shrink.ringEquiv K
  let h := (Shrink.homeomorph K).symm
  have hnhds (s : Set (Shrink.{0} K)) :
      s ∈ 𝓝 (0 : Shrink.{0} K) ↔ h '' s ∈ 𝓝 (0 : K) := by
    have h0 : h (0 : Shrink.{0} K) = (0 : K) := by
      exact map_zero e
    calc
      s ∈ 𝓝 (0 : Shrink.{0} K) ↔
          h ⁻¹' (h '' s) ∈ 𝓝 (0 : Shrink.{0} K) := by
            simp
      _ ↔ h '' s ∈ map h (𝓝 (0 : Shrink.{0} K)) := Iff.rfl
      _ ↔ h '' s ∈ 𝓝 (0 : K) := by simp [h0]
  have basisK (t : Set K) :
      t ∈ 𝓝 (0 : K) ↔
        ∃ a : K, a ≠ 0 ∧ {z : K | valuation K z < valuation K a} ⊆ t := by
    rw [IsValuativeTopology.mem_nhds_zero_iff]
    constructor
    · rintro ⟨γ, hγ⟩
      obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
      refine ⟨a, ?_, ?_⟩
      · grind [γ.ne_zero]
      · simpa [ha] using hγ
    · rintro ⟨a, ha0, hsub⟩
      refine ⟨Units.mk0 (valuation K a) (by simpa using ha0), ?_⟩
      exact hsub
  have basisSmall (s : Set (Shrink.{0} K)) :
      (∃ γ : (ValueGroupWithZero (Shrink.{0} K))ˣ,
        {z : Shrink.{0} K | valuation (Shrink.{0} K) z < γ} ⊆ s) ↔
      ∃ a : Shrink.{0} K, a ≠ 0 ∧
        {z : Shrink.{0} K |
          valuation (Shrink.{0} K) z < valuation (Shrink.{0} K) a} ⊆ s := by
    constructor
    · rintro ⟨γ, hγ⟩
      obtain ⟨a, ha⟩ :=
        ValuativeRel.valuation_surjective (γ : ValueGroupWithZero (Shrink.{0} K))
      refine ⟨a, ?_, ?_⟩
      · grind [γ.ne_zero]
      · simpa [ha] using hγ
    · rintro ⟨a, ha0, hsub⟩
      refine ⟨Units.mk0 (valuation (Shrink.{0} K) a) (by simpa using ha0), ?_⟩
      exact hsub
  apply IsValuativeTopology.of_zero
  intro s
  rw [hnhds s, basisK, basisSmall]
  constructor
  · rintro ⟨a, ha0, hsub⟩
    refine ⟨e.symm a, by simpa using ha0, ?_⟩
    intro z hz
    have hzK : e z ∈ h '' s := by
      apply hsub
      have hv := (shrinkLocalField_valuation_lt_iff K z (e.symm a)).mp hz
      change valuation K (e z) < valuation K (e (e.symm a)) at hv
      simpa using hv
    change e z ∈ e '' s at hzK
    rcases hzK with ⟨w, hw, hew⟩
    simpa [e.injective hew] using hw
  · rintro ⟨a, ha0, hsub⟩
    refine ⟨e a, by simpa using ha0, ?_⟩
    intro z hz
    have hzS : e.symm z ∈ s := hsub (by
      apply (shrinkLocalField_valuation_lt_iff K (e.symm z) a).2
      change valuation K (e (e.symm z)) < valuation K (e a)
      change valuation K z < valuation K (e a) at hz
      simpa using hz)
    exact ⟨e.symm z, hzS, e.apply_symm_apply z⟩

/-- The small representative of a nonarchimedean local field is itself a
nonarchimedean local field for the transported structures. -/
theorem shrinkLocalField_isNonarchimedeanLocalField :
    letI : Small.{0} K := smallLocalField K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    IsNonarchimedeanLocalField (Shrink.{0} K) := by
  let := smallLocalField K
  solve_by_elim [shrinkLocalField_isValuativeTopology, shrinkLocalField_locallyCompact, shrinkLocalField_isNontrivial, shrinkLocalFieldValuativeRel, mk, IsNonarchimedeanLocalField.mk]

section ValuationExtension

universe v w x y

end ValuationExtension

end LocalFieldTheory

end
