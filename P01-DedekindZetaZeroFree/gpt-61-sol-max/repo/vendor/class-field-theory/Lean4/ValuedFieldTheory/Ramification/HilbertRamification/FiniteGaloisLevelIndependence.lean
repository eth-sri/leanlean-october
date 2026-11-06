module

public import Mathlib

public import ValuedFieldTheory.Ramification.HilbertRamification.FiniteGaloisLevel

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Choice independence at finite Galois levels

The ramification filtration of a finite extension depends only on its
valuation ring.  For a finite Galois level over a complete discretely valued
field, uniqueness of the extended valuation therefore identifies the
filtration formed from the chosen integral-closure target with the filtration
formed from any other complete-DVF target extending the base valuation.
-/

noncomputable section

universe u v w x y z

namespace RamificationTheory.HilbertRamification.Higher

open ValuationTheory
open ValuationTheory.DiscreteValuationField


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : DVF.{u, v} K}
variable {target : DVF.{w, x} L} {target' : DVF.{w, y} L}
variable [base.valuation.HasExtension target.valuation]
variable [base.valuation.HasExtension target'.valuation]

private theorem lowerRamificationFiltration_ext
    {G : Type z} [Group G]
    {F F' :
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration G}
    (h : F.lower = F'.lower) :
    F = F' := by
  cases F
  cases F'
  cases h
  rfl

section
variable (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring)
include huniq huniq' hvaluationSubring
/-- Real lower ramification groups are unchanged when the two target
valuations have the same valuation ring. -/
theorem lowerRamificationGroup_eq_of_valuationSubring_eq
     
    (s : ℝ) :
    lowerRamificationGroup
        (base := base) (target := target) huniq s =
      lowerRamificationGroup
        (base := base) (target := target') huniq' s := by
  let e : target.valuationSubring ≃+* target'.valuationSubring :=
    { toFun := fun a => ⟨(a : L), by
        rw [← hvaluationSubring]
        exact a.property⟩
      invFun := fun a => ⟨(a : L), by
        rw [hvaluationSubring]
        exact a.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        rfl
      map_add' := by
        intro a b
        apply Subtype.ext
        rfl }
  let : IsLocalHom
      (e : target.valuationSubring →+* target'.valuationSubring) :=
    e.surjective.isLocalHom
  have hcomap :
      Ideal.comap
          (e : target.valuationSubring →+* target'.valuationSubring)
          target'.maximalIdeal =
        target.maximalIdeal := by
    ext a
    change e a ∈ target'.maximalIdeal ↔ a ∈ target.maximalIdeal
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  have hmap :
      Ideal.map
          (e : target.valuationSubring →+* target'.valuationSubring)
          target.maximalIdeal =
        target'.maximalIdeal := by
    rw [← hcomap]
    exact target'.maximalIdeal.map_comap_of_surjective
      (e : target.valuationSubring →+* target'.valuationSubring)
      e.surjective
  have hmap_real :
      Ideal.map
          (e : target.valuationSubring →+* target'.valuationSubring)
          (realRamificationIdeal target s) =
        realRamificationIdeal target' s := by
    simp only [realRamificationIdeal, Ideal.map_pow, hmap]
  have he_aut (σ : Gal(L/K)) (a : target.valuationSubring) :
      e (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a) =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target') huniq' σ (e a) := by
    ext
    rfl
  ext σ
  rw [mem_lowerRamificationGroup_iff, mem_lowerRamificationGroup_iff]
  constructor
  · intro hσ a'
    obtain ⟨a, rfl⟩ := e.surjective a'
    have ha := hσ a
    have hemap :
        e (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) ∈
          Ideal.map
            (e : target.valuationSubring →+* target'.valuationSubring)
            (realRamificationIdeal target s) :=
      Ideal.mem_map_of_mem _ ha
    rw [hmap_real] at hemap
    exact hemap
  · intro hσ a
    have ha' := hσ (e a)
    have hemap :
        e (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) ∈
          realRamificationIdeal target' s := ha'
    rw [← hmap_real] at hemap
    rcases (Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target'.valuationSubring)
      e.surjective).1 hemap with ⟨b, hb, hbe⟩
    have hba  :=
      e.injective hbe
    simpa only [hba] using hb

/-- Integral lower ramification filtrations are unchanged when the two target
valuations have the same valuation ring. -/
theorem lowerRamificationFiltration_eq_of_valuationSubring_eq
      :
    lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq =
      lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target') huniq' := by
  apply lowerRamificationFiltration_ext
  funext n
  apply lowerRamificationGroup_eq_of_valuationSubring_eq <;> assumption
end























section
variable [FiniteDimensional K L]
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (huniq' : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, y, y} base target')
    (hvaluationSubring :
      target.valuation.valuationSubring = target'.valuation.valuationSubring)
include huniq huniq' hvaluationSubring
/-- Inverse Herbrand functions are unchanged when the two target valuations
have the same valuation ring. -/
theorem inverseHerbrandFunction_eq_of_valuationSubring_eq
      :
    inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq =
      inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target') huniq' := by
  have hF :=
    lowerRamificationFiltration_eq_of_valuationSubring_eq
      huniq huniq' hvaluationSubring
  exact congrArg
    (fun F =>
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction F)
    hF

/-- Upper ramification groups are unchanged when the two target valuations
have the same valuation ring. -/
theorem upperRamificationGroup_eq_of_valuationSubring_eq
     
    (t : ℝ) :
    upperRamificationGroupOfUniqueExtension
        (base := base) (target := target) huniq t =
      upperRamificationGroupOfUniqueExtension
        (base := base) (target := target') huniq' t := by
  change lowerRamificationGroup (base := base) (target := target) huniq
      (inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq t) =
    lowerRamificationGroup (base := base) (target := target') huniq'
      (inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target') huniq' t)
  rw [inverseHerbrandFunction_eq_of_valuationSubring_eq
    huniq huniq' hvaluationSubring]
  exact lowerRamificationGroup_eq_of_valuationSubring_eq
    huniq huniq' hvaluationSubring _
end


end RamificationTheory.HilbertRamification.Higher

namespace RamificationTheory.HilbertRamification.FiniteGaloisLevel

open ValuationTheory
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]












































































































































end RamificationTheory.HilbertRamification.FiniteGaloisLevel

end
