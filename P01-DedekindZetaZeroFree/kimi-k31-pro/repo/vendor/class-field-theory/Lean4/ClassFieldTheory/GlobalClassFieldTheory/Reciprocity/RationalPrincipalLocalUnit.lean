module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalPrimeFactorization
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition
public import ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
public import ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/















set_option autoImplicit false

/-!
# The ramified local unit of a rational principal idele

For a nonzero rational number `x` and a rational prime `p`, removing the
`p`-power from `x` produces an actual `p`-adic unit.  This file identifies
that unit simultaneously in the height-one completion used by global
reciprocity, in the standard field `ℚ_[p]`, and in the valuation subring
used by the multiplicative Lubin--Tate construction.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open LocalFieldTheory.DiscreteValuationField.Examples.Qp

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩



/-- The rational `p`-unit, expressed as a unit of the valuation subring of
the standard local field `ℚ_[p]`. -/
def rationalPrimeUnitValuationSubringUnit
    (x : ℚˣ) (p : Nat.Primes) :
    (padicLocalField p.1).valuationSubringˣ :=
  Units.map
      (padicIntEquivValuationSubring
        p.1).toMonoidHom
    (padicIntUnitOfRat p
      (rationalPrimeUnit x p : ℚ)
      (Units.ne_zero _)
      (padicValRat_rationalPrimeUnit x p))

/-- Forgetting the integrality proof from the standard valuation-subring
unit recovers the rational `p`-unit in `ℚ_[p]`. -/
@[simp]
theorem rationalPrimeUnitValuationSubringUnit_coe
    (x : ℚˣ) (p : Nat.Primes) :
    ((rationalPrimeUnitValuationSubringUnit x p :
        (padicLocalField p.1).valuationSubring) :
      ℚ_[p.1]) =
        ((rationalPrimeUnit x p : ℚ) : ℚ_[p.1]) := by
  change
    ((padicIntEquivValuationSubring p.1
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (Units.ne_zero _)
          (padicValRat_rationalPrimeUnit x p)) :
        (padicLocalField p.1).valuationSubring) :
      ℚ_[p.1]) =
        ((rationalPrimeUnit x p : ℚ) : ℚ_[p.1])
  rw [
    padicIntEquivValuationSubring_coe,
    padicIntUnitOfRat_coe]

/-- The Lubin--Tate field-unit inclusion of the rational `p`-unit is the
ordinary embedding of that rational unit into `ℚ_[p]`. -/
theorem standardLubinTateUnitFactorFieldUnit_rationalPrimeUnit
    (x : ℚˣ) (p : Nat.Primes) :
    LubinTate.standardLubinTateUnitFactorFieldUnit
        (padicLocalField p.1)
        (rationalPrimeUnitValuationSubringUnit x p) =
      Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom
        (rationalPrimeUnit x p) := by
  apply Units.ext
  change
    ((rationalPrimeUnitValuationSubringUnit x p :
        (padicLocalField p.1).valuationSubring) :
      ℚ_[p.1]) =
        algebraMap ℚ ℚ_[p.1] (rationalPrimeUnit x p : ℚ)
  exact rationalPrimeUnitValuationSubringUnit_coe x p

/-- The standard multiplicative Lubin--Tate base uniformizer is exactly the
image of the positive rational prime generator in `ℚ_[p]ˣ`. -/
theorem standardLubinTateBaseUniformizerUnit_eq_rationalPrimeGenerator
    (p : Nat.Primes) :
    LubinTate.standardLubinTateBaseUniformizerUnit
        (LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
          p.1) =
      Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom
        (Units.mk0 (p.1 : ℚ) (by
          exact_mod_cast p.2.ne_zero)) := by
  apply Units.ext
  change
    ((padicIntEquivValuationSubring
        p.1 (p.1 : ℤ_[p.1]) :
      (padicLocalField p.1).valuationSubring) :
        ℚ_[p.1]) =
      algebraMap ℚ ℚ_[p.1] (p.1 : ℚ)
  rw [padicIntEquivValuationSubring_coe]
  simp

/-- Restoring the removed `p`-power recovers the original rational field
unit.  This is the multiplicative factorization used after completion. -/
theorem rationalPrimeUnit_mul_primeGenerator_zpow
    (x : ℚˣ) (p : Nat.Primes) :
    rationalPrimeUnit x p *
        (Units.mk0 (p.1 : ℚ) (by
          exact_mod_cast p.2.ne_zero)) ^
          padicValRat p.1 (x : ℚ) =
      x := by
  rw [rationalPrimeUnit]
  calc
    ((Units.mk0 (p.1 : ℚ) (by
          exact_mod_cast p.2.ne_zero)) ^
        (-padicValRat p.1 (x : ℚ)) * x) *
          (Units.mk0 (p.1 : ℚ) (by
            exact_mod_cast p.2.ne_zero)) ^
            padicValRat p.1 (x : ℚ) =
        x * ((Units.mk0 (p.1 : ℚ) (by
              exact_mod_cast p.2.ne_zero)) ^
            (-padicValRat p.1 (x : ℚ)) *
          (Units.mk0 (p.1 : ℚ) (by
              exact_mod_cast p.2.ne_zero)) ^
            padicValRat p.1 (x : ℚ)) := by
      ac_rfl
    _ = x := by
      rw [← zpow_add]
      simp

/-- In `ℚ_[p]ˣ`, a rational field unit is its actual integral
`rationalPrimeUnit` factor times the corresponding power of the standard
multiplicative Lubin--Tate uniformizer. -/
theorem rationalPadicFieldUnit_eq_unitFactor_mul_baseUniformizer_zpow
    (x : ℚˣ) (p : Nat.Primes) :
    Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x =
      LubinTate.standardLubinTateUnitFactorFieldUnit
          (padicLocalField p.1)
          (rationalPrimeUnitValuationSubringUnit x p) *
        LubinTate.standardLubinTateBaseUniformizerUnit
            (LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
              p.1) ^
          padicValRat p.1 (x : ℚ) := by
  rw [
    standardLubinTateUnitFactorFieldUnit_rationalPrimeUnit,
    standardLubinTateBaseUniformizerUnit_eq_rationalPrimeGenerator,
    ← map_zpow,
    ← map_mul,
    rationalPrimeUnit_mul_primeGenerator_zpow]

/-- The exponent selected by the complete-DVF uniformizer decomposition of a
rational element is its ordinary `p`-adic valuation. -/
theorem rationalPadicFieldUnit_uniformizerValueExponent
    (x : ℚˣ) (p : Nat.Primes) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent
        (padicLocalField p.1).toCompleteDVF)
        (LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
          p.1)
        (Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x) =
      padicValRat p.1 (x : ℚ) := by
  let F := padicLocalField p.1
  let hπ :=
    LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
      p.1
  let X : ℚ_[p.1]ˣ :=
    Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x
  let u : F.valuationSubringˣ :=
    rationalPrimeUnitValuationSubringUnit x p
  let ϖ : ℚ_[p.1]ˣ :=
    LubinTate.standardLubinTateBaseUniformizerUnit hπ
  let V :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer
      F.toCompleteDVF) hπ
  have hfactor :
      X =
        LubinTate.standardLubinTateUnitFactorFieldUnit F u *
          ϖ ^ padicValRat p.1 (x : ℚ) := by
    simpa only [F, hπ, X, u, ϖ] using
      rationalPadicFieldUnit_eq_unitFactor_mul_baseUniformizer_zpow
        x p
  have huMem :
      LubinTate.standardLubinTateUnitFactorFieldUnit F u ∈
        F.valuation.valuationSubring.unitGroup := by
    simpa only [
      LubinTate.standardLubinTateUnitFactorFieldUnit] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits_mem_unitGroup
        F.toCompleteDVF u)
  have hzero :
      V.zeroSubgroup =
        F.valuation.valuationSubring.unitGroup := by
    simpa only [V] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup
        F.toCompleteDVF hπ)
  have huZero :
      V.val
          (LubinTate.standardLubinTateUnitFactorFieldUnit F u) =
        0 := by
    apply (V.mem_zeroSubgroup_iff _).1
    rw [hzero]
    exact huMem
  have hϖeq :
      ϖ =
        Units.mk0
          ((padicIntEquivValuationSubring
              p.1 (p.1 : ℤ_[p.1]) :
            (padicLocalField p.1).valuationSubring) :
            ℚ_[p.1])
          hπ.ne_zero := by
    apply Units.ext
    change
      (ϖ : ℚ_[p.1]) =
        ((padicIntEquivValuationSubring
            p.1 (p.1 : ℤ_[p.1]) :
          (padicLocalField p.1).valuationSubring) :
          ℚ_[p.1])
    simpa only [ϖ] using
      LubinTate.standardLubinTateBaseUniformizerUnit_coe hπ
  have hϖ : V.IsUniformizer ϖ := by
    rw [hϖeq]
    simpa only [V] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer
        F.toCompleteDVF hπ)
  change V.val X = padicValRat p.1 (x : ℚ)
  rw [
    hfactor,
    V.val_mul,
    V.val_uniformizer_zpow hϖ,
    huZero,
    zero_add]

/-- The actual unit part chosen by the standard multiplicative Lubin--Tate
uniformizer decomposition of a rational `p`-adic field unit is precisely
`rationalPrimeUnitValuationSubringUnit`. -/
theorem rationalPadicFieldUnit_uniformizerUnitPart
    (x : ℚˣ) (p : Nat.Primes) :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart
        (padicLocalField p.1).toCompleteDVF
        (LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
          p.1)
        (Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x) =
      rationalPrimeUnitValuationSubringUnit x p := by
  let F := padicLocalField p.1
  let hπ :=
    LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
      p.1
  let X : ℚ_[p.1]ˣ :=
    Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x
  let u : F.valuationSubringˣ :=
    rationalPrimeUnitValuationSubringUnit x p
  let ϖ : ℚ_[p.1]ˣ :=
    LubinTate.standardLubinTateBaseUniformizerUnit hπ
  apply
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_injective
  refine
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
      F.toCompleteDVF hπ X).trans ?_
  change
    X * ϖ ^
        (-((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent
          F.toCompleteDVF) hπ X)) =
      LubinTate.standardLubinTateUnitFactorFieldUnit F u
  rw [
    show
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent
          F.toCompleteDVF) hπ X =
        padicValRat p.1 (x : ℚ) by
        simpa only [F, hπ, X] using
          rationalPadicFieldUnit_uniformizerValueExponent x p,
    show
      X =
        LubinTate.standardLubinTateUnitFactorFieldUnit F u *
          ϖ ^ padicValRat p.1 (x : ℚ) by
        simpa only [F, hπ, X, u, ϖ] using
          rationalPadicFieldUnit_eq_unitFactor_mul_baseUniformizer_zpow
            x p]
  rw [mul_assoc, ← zpow_add]
  simp













end Reciprocity
end GlobalClassFieldTheory

end
