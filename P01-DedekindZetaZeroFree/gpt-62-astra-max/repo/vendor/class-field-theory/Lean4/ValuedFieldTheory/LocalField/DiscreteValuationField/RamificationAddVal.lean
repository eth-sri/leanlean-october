module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Additive valuations in finite complete-DVF extensions

The normalized additive valuation on the target valuation ring restricts to
the ramification index times the normalized additive valuation on the base
valuation ring.  The proof is characteristic-independent and follows from the
ideal identity
`m_K · O_L = m_L ^ e`.
-/

noncomputable section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace ValuedExtension
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The target normalized additive valuation of an element from the base
valuation ring is its base additive valuation multiplied by the ramification
index.  This includes the zero element, whose additive valuation is `⊤`. -/
theorem addVal_integerMap_eq_ramificationIndex_nsmul
    (a : base.valuationSubring) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (integerMap base.toDVF target.toDVF a) =
      ramificationIndex base.toDVF target.toDVF •
        IsDiscreteValuationRing.addVal base.valuationSubring a := by
  let e := ramificationIndex base.toDVF target.toDVF
  have he_ne : e ≠ 0 := by
    intro he
    have hle :=
      maximalIdeal_map_integerMap_le base.toDVF target.toDVF
    have hmap :=
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
        base target
    rw [show ramificationIndex base.toDVF target.toDVF = e from rfl,
      he, pow_zero] at hmap
    rw [hmap] at hle
    refine
      (IsLocalRing.maximalIdeal.isMaximal
        target.valuationSubring).ne_top (top_unique ?_)
    simpa using hle
  by_cases ha : a = 0
  · subst a
    have he_coe_ne : (e : ℕ∞) ≠ 0 := by
      exact_mod_cast he_ne
    rw [map_zero, IsDiscreteValuationRing.addVal_zero,
      IsDiscreteValuationRing.addVal_zero, nsmul_eq_mul,
      ENat.mul_top he_coe_ne]
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible base.valuationSubring
  obtain ⟨varpi, hvarpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  obtain ⟨m, unit, ha_decomp⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hpi
  have hspan :
      Ideal.span
          ({integerMap base.toDVF target.toDVF pi} :
            Set target.valuationSubring) =
        Ideal.span ({varpi ^ e} : Set target.valuationSubring) := by
    calc
      _ =
          Ideal.map (integerMap base.toDVF target.toDVF)
            (Ideal.span ({pi} : Set base.valuationSubring)) := by
              simp [Ideal.map_span]
      _ = Ideal.map (integerMap base.toDVF target.toDVF)
          base.maximalIdeal := by
            simp [hpi.maximalIdeal_eq]
      _ = target.maximalIdeal ^ e := maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
                base target
      _ = Ideal.span ({varpi ^ e} : Set target.valuationSubring) := by
            rw [show target.maximalIdeal =
                IsLocalRing.maximalIdeal target.valuationSubring from rfl,
              hvarpi.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hmap_uniformizer :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (integerMap base.toDVF target.toDVF pi) =
        e := by
    calc
      _ =
          IsDiscreteValuationRing.addVal target.valuationSubring
            (varpi ^ e) :=
        (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2
          (Ideal.span_singleton_eq_span_singleton.mp hspan)
      _ = e := hvarpi.addVal_pow e
  rw [ha_decomp, map_mul, map_pow,
    IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, hmap_uniformizer,
    IsDiscreteValuationRing.addVal_def
      ((unit : base.valuationSubring) * pi ^ m)
      unit hpi m rfl]
  have hmap_unit := IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
        (unit.isUnit.map
          (integerMap base.toDVF target.toDVF))
  rw [hmap_unit, zero_add]
  simp [e, nsmul_eq_mul, mul_comm]

/-- The target additive valuation of the image of a base uniformizer is the
ramification index. -/
theorem addVal_integerMap_eq_ramificationIndex_of_irreducible
    {a : base.valuationSubring} (ha : Irreducible a) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (integerMap base.toDVF target.toDVF a) =
      (ramificationIndex base.toDVF target.toDVF : ℕ∞) := by
  simp_all [addVal_integerMap_eq_ramificationIndex_nsmul]

/-- If a base uniformizer remains a uniformizer after applying the
valuation-ring map, then the relative ramification index is one. -/
theorem ramificationIndex_eq_one_of_integerMap_uniformizer
    (a : base.valuationSubring)
    (ha : base.valuation.IsUniformizer (a : K))
    (hmap :
      target.valuation.IsUniformizer
        ((integerMap base.toDVF target.toDVF a :
          target.valuationSubring) : L)) :
    ramificationIndex base.toDVF target.toDVF = 1 := by
  have hadd :=
    addVal_integerMap_eq_ramificationIndex_nsmul base target a
  rw [IsDiscreteValuationRing.addVal_uniformizer ((IsDiscreteValuationRing.irreducible_iff_uniformizer
    (integerMap base.toDVF target.toDVF a)).2
    (target.maximalIdeal_eq_span_uniformizer hmap)),
    IsDiscreteValuationRing.addVal_uniformizer ((IsDiscreteValuationRing.irreducible_iff_uniformizer a).2
      (base.maximalIdeal_eq_span_uniformizer ha)),
    nsmul_eq_mul, mul_one] at hadd
  exact_mod_cast hadd.symm

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
