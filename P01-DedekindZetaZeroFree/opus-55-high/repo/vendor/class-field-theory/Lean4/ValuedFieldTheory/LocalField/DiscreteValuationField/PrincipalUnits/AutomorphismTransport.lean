module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
public import Mathlib.Algebra.Group.Units.Equiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Automorphism transport for principal units

A field automorphism preserving the chosen valuation ring acts on the valuation ring,
its residue field, its units, and every principal-unit quotient.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- A field automorphism preserving the chosen valuation ring induces a ring
automorphism of the valuation ring.  This is the unit/residue source used
before invoking local reciprocity in the local-field arguments. -/
def valuationSubringRingEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring) :
    F.valuationSubring ≃+* F.valuationSubring :=
  RingEquiv.restrict e F.valuation.valuationSubring
    F.valuation.valuationSubring hmem

/-- A valuation-ring-preserving field automorphism preserves every power of the
maximal ideal of the chosen valuation ring. -/
theorem valuationSubringRingEquivOfPreserves_mem_maximalIdeal_pow_iff
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (x : F.valuationSubring) :
    valuationSubringRingEquivOfPreserves F e hmem x ∈ F.maximalIdeal ^ n ↔
      x ∈ F.maximalIdeal ^ n := by
  let r := valuationSubringRingEquivOfPreserves F e hmem
  have hmax :
      F.maximalIdeal.map
          (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal r
  have hmap :
      (F.maximalIdeal ^ n).map (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal ^ n := by
    rw [Ideal.map_pow, hmax]
  constructor
  · intro hx
    rw [← hmap] at hx
    rw [Ideal.mem_map_iff_of_surjective
      (r : F.valuationSubring →+* F.valuationSubring) r.surjective] at hx
    rcases hx with ⟨y, hy, hyx⟩
    have hy_eq : y = x := r.injective hyx
    simpa [hy_eq] using hy
  · intro hx
    rw [← hmap]
    exact Ideal.mem_map_of_mem (r : F.valuationSubring →+* F.valuationSubring) hx
