module

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitExp

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
Restricts the logarithm series to principal units and places its values in the corresponding
additive ideal.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The logarithm-series value of a first principal unit `u`, defined as the
series for `log(1 + (u - 1))`. -/
def principalUnitLogSeriesOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) : K :=
  logOnePlusSeriesFieldOfWithZeroValuation v
    (principalUnitSubOneOfWithZeroValuation v u) hnK

/-- Sharp ramified endpoint form of the logarithm: if `u ∈ U^n` and
`n > e/(p-1)`, then `Log(u)` lies in `m^n`. -/
def principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) n) :
    ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
      Ideal (completeDVFOfWithZeroValuation v).valuationSubring) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let aSub : F.valuationSubring :=
    ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
  let x : K := (aSub : K)
  have haMem : aSub ∈ F.maximalIdeal ^ n := by
    simpa [aSub] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
        (F := F) n (u : F.valuationSubringˣ)).1 u.property
  have hxthreshold :
      ∀ hx : x ≠ 0,
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
    intro hx
    have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      simpa [F, x] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n aSub haMem hx
    exact lt_of_lt_of_le hlevel (by exact_mod_cast hge)
  have haMemOne : aSub ∈ F.maximalIdeal := by
    have hle : F.maximalIdeal ^ n ≤ F.maximalIdeal ^ 1 :=
      Ideal.pow_le_pow_right hn
    simpa [pow_one] using hle haMem
  have hxlt : v x < (1 : WithZero (Multiplicative ℤ)) := by
    have hbound := (CompleteDVF.mem_maximalIdeal_iff F aSub).1 haMemOne
    change v (aSub : K) < 1 at hbound
    exact hbound
  have hbLe :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) ≤
        (1 : WithZero (Multiplicative ℤ)) := by
    by_cases hx : x = 0
    · simp [x, hx]
    · have hv :
          v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) = v x :=
        valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval
          hxlt (hxthreshold hx) hcomplete
      have hxInt : v x ≤ (1 : WithZero (Multiplicative ℤ)) :=
        le_of_lt hxlt
      simpa [hv] using hxInt
  let b : F.valuationSubring :=
    ⟨logOnePlusSeriesFieldOfWithZeroValuation v x hnK,
      (CompleteDVF.mem_valuationSubring_iff F
        (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)).2
        (by
          change v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) ≤ 1
          exact hbLe)⟩
  have hbmem : b ∈ F.maximalIdeal ^ n := by
    apply
      mem_maximalIdeal_pow_ofWithZeroValuation_val_ge
        (v := v) (π := π) hπ hπval n b
    intro hbne
    by_cases hx : x = 0
    · have hbzero : (b : K) = 0 := by
        simp [b, x, hx]
      exact False.elim (hbne hbzero)
    · have hv :
          v (b : K) = v x := by
        simpa [b] using
          valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
            (v := v) (p := p) e (x := x) hx hnK hnval
            hxlt (hxthreshold hx) hcomplete
      have hge :
          (n : ℤ) ≤
            (ofWithZeroValuation v).val (Units.mk0 x hx) := by
        simpa [F, x] using
          ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
            (v := v) (π := π) hπ hπval n aSub haMem hx
      simp_all
  exact ⟨b, hbmem⟩

/-- Endpoint package for the deep exponential–logarithm equivalence as the actual group isomorphism:
if the evaluated composites are identities, then the source and target groups are
multiplicatively isomorphic after wrapping the additive ideal by
`Multiplicative`.  The multiplicativity of the forward map is supplied by the
scaled exponential additivity proved above. -/
def principalUnitExpLogMulEquivOfExact_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Algebra ℚ K]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnKexp : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hnKlog : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hlog_exp :
      ∀ a :
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal (completeDVFOfWithZeroValuation v).valuationSubring),
        principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKexp hnvalExp hcomplete a) =
        a)
    (hexp_log :
      ∀ u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) n,
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKexp hnvalExp hcomplete
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKlog hnvalLog hcomplete u) =
        u) :
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃*
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) n where
  toFun a :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hcomplete a.toAdd
  invFun u :=
    Multiplicative.ofAdd
      (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hcomplete u)
  left_inv a := by
    apply Multiplicative.ext
    simpa using hlog_exp a.toAdd
  right_inv u := by
    simpa using hexp_log u
  map_mul' a b := by
    simpa using
      principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hcomplete a.toAdd b.toAdd
