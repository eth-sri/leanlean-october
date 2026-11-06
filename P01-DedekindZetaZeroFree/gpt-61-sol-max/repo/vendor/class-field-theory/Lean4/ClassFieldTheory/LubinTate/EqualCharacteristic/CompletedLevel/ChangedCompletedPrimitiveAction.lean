module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# The completed theta-intertwining theorem: primitive action for the changed completed level

The theta relation in the completed theta-intertwining theorem uses the source parameter `u⁻¹T`.  We first
prove, genuinely by Eisenstein over `(AlgebraicClosure κ)[[T]]`, that its
primitive polynomial stays irreducible over the completed maximal-unramified
Laurent field.  We then enumerate its roots by source Lubin--Tate unit
brackets and show that every such primitive point generates the splitting
field.

The theta unit `u` and a source Lubin--Tate bracket unit `a` are deliberately
kept as distinct parameters.  Repository index `n` is division level `n + 1`.
-/

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]







/-- The image of the source unit `u⁻¹` in
`(AlgebraicClosure κ)[[T]]`. -/
noncomputable def equalCharacteristicChangedCompletedSourceUnit
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) :
    (AlgebraicClosure F.residueField)⟦X⟧ˣ :=
  Units.map
    (PowerSeries.map
      (algebraMap F.residueField (AlgebraicClosure F.residueField)))
    (equalCharacteristicThetaSourceUnit u)

/-- The integral primitive polynomial for source parameter `u⁻¹T`,
after coefficientwise extension to `(AlgebraicClosure κ)[[T]]`. -/
noncomputable def equalCharacteristicChangedCompletedIntegralPrimitivePolynomial
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Polynomial (AlgebraicClosure F.residueField)⟦X⟧ :=
  (equalCharacteristicChangedIntegralPrimitivePolynomial F
      (equalCharacteristicThetaSourceUnit u) n).map
    (PowerSeries.map
      (algebraMap F.residueField (AlgebraicClosure F.residueField)))

/-- The changed integral primitive polynomial remains monic after scalar extension. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).Monic :=
  (equalCharacteristicChangedIntegralPrimitivePolynomial_monic F
    (equalCharacteristicThetaSourceUnit u) n).map _

/-- The completed integral primitive polynomial has degree `(q - 1) * q ^ n`. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).natDegree =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial,
    (equalCharacteristicChangedIntegralPrimitivePolynomial_monic F
      (equalCharacteristicThetaSourceUnit u) n).natDegree_map,
    equalCharacteristicChangedIntegralPrimitivePolynomial_natDegree]

/-- Passage from the changed integral polynomial to Laurent series agrees
with the completed coefficientwise base change. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_map
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).map
        (algebraMap (AlgebraicClosure F.residueField)⟦X⟧
          (equalCharacteristicCompletedUnramifiedField F.residueField)) =
      equalCharacteristicChangedCompletedPrimitivePolynomial F u n := by
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial,
    Polynomial.map_map,
    equalCharacteristicPowerSeriesLaurent_baseChange_commutes,
    ← Polynomial.map_map]
  rfl

/-- Modulo `T`, the completed changed primitive polynomial is its single
leading monomial. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_map_constantCoeff
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).map
        (PowerSeries.constantCoeff
          (R := AlgebraicClosure F.residueField)) =
      Polynomial.X ^
        ((Nat.card F.residueField - 1) * Nat.card F.residueField ^ n) := by
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial,
    Polynomial.map_map]
  have hcomp :
      (PowerSeries.constantCoeff
          (R := AlgebraicClosure F.residueField)).comp
          (PowerSeries.map
            (algebraMap F.residueField (AlgebraicClosure F.residueField))) =
        (algebraMap F.residueField (AlgebraicClosure F.residueField)).comp
          (PowerSeries.constantCoeff (R := F.residueField)) := by
    ext f
    simp only [RingHom.comp_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]
  rw [hcomp, ← Polynomial.map_map,
    equalCharacteristicChangedIntegralPrimitivePolynomial_map_constantCoeff]
  simp

/-- The constant coefficient is the mapped unit times `T`, rather than
merely `T`; this is the point at which the source `u⁻¹T` matters. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).coeff 0 =
      (equalCharacteristicChangedCompletedSourceUnit F u :
        (AlgebraicClosure F.residueField)⟦X⟧) * PowerSeries.X := by
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial,
    Polynomial.coeff_map,
    equalCharacteristicChangedIntegralPrimitivePolynomial_coeff_zero]
  simp [equalCharacteristicChangedIntegralUniformizer,
    equalCharacteristicChangedCompletedSourceUnit]

private theorem equalCharacteristicChangedCompletedIntegralUniformizer_notMem_span_X_sq
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedCompletedSourceUnit F u :
        (AlgebraicClosure F.residueField)⟦X⟧) * PowerSeries.X ∉
      (Ideal.span
        ({PowerSeries.X} :
          Set (AlgebraicClosure F.residueField)⟦X⟧)) ^ 2 := by
  intro h
  let a := equalCharacteristicChangedCompletedSourceUnit F u
  have hmul :=
    ((Ideal.span
      ({PowerSeries.X} :
        Set (AlgebraicClosure F.residueField)⟦X⟧)) ^ 2).mul_mem_left
      ((a⁻¹ : (AlgebraicClosure F.residueField)⟦X⟧ˣ) :
        (AlgebraicClosure F.residueField)⟦X⟧) h
  have hcancel :
      ((a⁻¹ : (AlgebraicClosure F.residueField)⟦X⟧ˣ) :
        (AlgebraicClosure F.residueField)⟦X⟧) *
          ((a : (AlgebraicClosure F.residueField)⟦X⟧) * PowerSeries.X) =
        PowerSeries.X := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hcancel] at hmul
  exact powerSeries_X_notMem_span_X_sq
    (AlgebraicClosure F.residueField) hmul

/-- The completed integral source polynomial is genuinely Eisenstein at
`(T)`. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_isEisensteinAt
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).IsEisensteinAt
      (Ideal.span
        ({PowerSeries.X} :
          Set (AlgebraicClosure F.residueField)⟦X⟧)) := by
  let Q := equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n
  let d := (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n
  have hmonic : Q.Monic :=
    equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_monic F u n
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    PowerSeries.span_X_isPrime.ne_top ?_ ?_
  · intro i hi
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have hcoeff :
        PowerSeries.constantCoeff
            ((equalCharacteristicChangedCompletedIntegralPrimitivePolynomial
              F u n).coeff i) =
          (Polynomial.X ^ d :
            Polynomial (AlgebraicClosure F.residueField)).coeff i := by
      simpa only [Polynomial.coeff_map, d] using
        congrArg
          (fun p : Polynomial (AlgebraicClosure F.residueField) ↦ p.coeff i)
          (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_map_constantCoeff
            F u n)
    have hid : i < d := by
      simpa [Q, d,
        equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_natDegree]
        using hi
    simpa [d, Polynomial.coeff_X_pow, ne_of_lt hid] using hcoeff
  · rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_coeff_zero]
    exact equalCharacteristicChangedCompletedIntegralUniformizer_notMem_span_X_sq F u

/-- The completed integral primitive polynomial is irreducible by Eisenstein's criterion. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Irreducible
      (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n) := by
  apply
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_isEisensteinAt
      F u n).irreducible
      PowerSeries.span_X_isPrime
      (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_monic
        F u n).isPrimitive
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)

/-- The source primitive polynomial remains irreducible over the completed
maximal-unramified Laurent field. -/
theorem equalCharacteristicChangedCompletedPrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Irreducible (equalCharacteristicChangedCompletedPrimitivePolynomial F u n) := by
  have hmap :
      Irreducible
        ((equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).map
          (algebraMap (AlgebraicClosure F.residueField)⟦X⟧
            (equalCharacteristicCompletedUnramifiedField F.residueField))) :=
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_monic
      F u n).irreducible_iff_irreducible_map_fraction_map.mp
      (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_irreducible
        F u n)
  rwa [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_map] at hmap





























































































































































































































































































































































































































































































































































end EqualCharacteristic
end LubinTate

end
