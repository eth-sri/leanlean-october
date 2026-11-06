module

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.InverseEstimates

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
Restricts the exponential series to deep additive ideals and shows that its values lie in the
corresponding principal-unit subgroups.
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

/-- The exponential-series value, viewed as a first principal unit. -/
def principalUnitExpSeriesOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  have hlt :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1) <
        (1 : WithZero (Multiplicative ℤ)) :=
    valuation_expSeriesField_sub_one_lt_one_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  let a : F.valuationSubring :=
    ⟨expSeriesFieldOfWithZeroValuation v x hnK - 1,
      (CompleteDVF.mem_valuationSubring_iff F
        (expSeriesFieldOfWithZeroValuation v x hnK - 1)).2
        (by
          change v (expSeriesFieldOfWithZeroValuation v x hnK - 1) ≤ 1
          exact le_of_lt hlt)⟩
  have ha : a ∈ F.maximalIdeal ^ 1 := by
    have ha0 : a ∈ F.maximalIdeal := by
      rw [CompleteDVF.mem_maximalIdeal_iff]
      change v (expSeriesFieldOfWithZeroValuation v x hnK - 1) < 1
      exact hlt
    simpa [pow_one] using ha0
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup
      F (n := 1) le_rfl a ha

/-- Sharp ramified endpoint form of the exponential: if `a ∈ m^n` and
`n > e/(p-1)`, then `Exp(a)` is a principal unit in `U^n`. -/
def principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) n := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let x : K := ((a : F.valuationSubring) : K)
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
          (v := v) (π := π) hπ hπval n
          (a := (a : F.valuationSubring)) a.property hx
    exact lt_of_lt_of_le hlevel (by exact_mod_cast hge)
  have hbLe :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1) ≤
        (1 : WithZero (Multiplicative ℤ)) := by
    by_cases hx : x = 0
    · simp [x, hx]
    · have hv :
          v (expSeriesFieldOfWithZeroValuation v x hnK - 1) = v x :=
        valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
          (v := v) (p := p) e (x := x) hx hnK hnval
          (hxthreshold hx) hcomplete
      have hxInt : v x ≤ (1 : WithZero (Multiplicative ℤ)) := by
        have hxMem : x ∈ F.valuation.valuationSubring := by
          change ((a : F.valuationSubring) : K) ∈ F.valuation.valuationSubring
          simp
        have hxBound := (CompleteDVF.mem_valuationSubring_iff F x).1 hxMem
        change v x ≤ 1 at hxBound
        exact hxBound
      simpa [hv] using hxInt
  let b : F.valuationSubring :=
    ⟨expSeriesFieldOfWithZeroValuation v x hnK - 1,
      (CompleteDVF.mem_valuationSubring_iff F
        (expSeriesFieldOfWithZeroValuation v x hnK - 1)).2
        (by
          change v (expSeriesFieldOfWithZeroValuation v x hnK - 1) ≤ 1
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
          valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
            (v := v) (p := p) e (x := x) hx hnK hnval
            (hxthreshold hx) hcomplete
      have hge :
          (n : ℤ) ≤
            (ofWithZeroValuation v).val (Units.mk0 x hx) := by
        simpa [F, x] using
          ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
            (v := v) (π := π) hπ hπval n
            (a := (a : F.valuationSubring)) a.property hx
      simp_all
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup
      F hn b hbmem

/--
The underlying field value of the scaled exponential-series principal unit is the corresponding
field exponential series.
-/
@[simp] theorem principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
    ((((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnK hnval hcomplete a : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n) :
        F.valuationSubringˣ) : F.valuationSubring) : K) =
      expSeriesFieldOfWithZeroValuation v
        (((a : F.valuationSubring) : K)) hnK := by
  simp [principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled]

/-- Scaled principal-unit exponential additivity on the sharp convergence threshold:
`Exp(a+b)=Exp(a)Exp(b)` for `a,b ∈ m^n`. -/
theorem principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a b :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnK hnval hcomplete (a + b) =
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete a *
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete b := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let x : K := ((a : F.valuationSubring) : K)
  let y : K := ((b : F.valuationSubring) : K)
  have hlevelR : (e : ℝ) / ((p : ℝ) - 1) < (n : ℝ) := by
    exact_mod_cast hlevel
  have hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) := by
    intro hx
    have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      simpa [F, x] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n
          (a := (a : F.valuationSubring)) a.property hx
    exact lt_of_lt_of_le hlevelR (by exact_mod_cast hge)
  have hythreshold : ∀ hy : y ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 y hy) : ℝ) := by
    intro hy
    have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 y hy) := by
      simpa [F, y] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n
          (a := (b : F.valuationSubring)) b.property hy
    exact lt_of_lt_of_le hlevelR (by exact_mod_cast hge)
  have hfield :
      expSeriesFieldOfWithZeroValuation v (x + y) hnK =
        expSeriesFieldOfWithZeroValuation v x hnK *
          expSeriesFieldOfWithZeroValuation v y hnK :=
    expSeriesField_add_eq_mul_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x y hnK hnval hxthreshold hythreshold
      hcomplete
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  simpa [F, x, y] using hfield

/-- The additive parameter `x = u - 1` attached to a first principal unit. -/
def principalUnitSubOneOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) : K :=
  (((u : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
      (completeDVFOfWithZeroValuation v).valuationSubring) : K) - 1

/-- A first principal unit has additive parameter of valuation strictly below
one, which is the convergence hypothesis for the logarithm series. -/
theorem principalUnitSubOne_val_lt_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) :
    v (principalUnitSubOneOfWithZeroValuation v u) <
      (1 : WithZero (Multiplicative ℤ)) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  have hu :
      ((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
        F.maximalIdeal := by
    have hmemPow :
        ((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
          F.maximalIdeal ^ 1 :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
        (F := F) 1 (u : F.valuationSubringˣ)).1 u.property
    simp_all
  have hlt := (CompleteDVF.mem_maximalIdeal_iff F
    (((u : F.valuationSubringˣ) : F.valuationSubring) - 1)).1 hu
  change v ((((u : F.valuationSubringˣ) : F.valuationSubring) - 1 :
    F.valuationSubring) : K) < (1 : WithZero (Multiplicative ℤ)) at hlt
  simpa [principalUnitSubOneOfWithZeroValuation, F] using hlt

/--
Establishes the identity `principalUnitSubOneOfWithZeroValuation v (1 :
(CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) = 0`.
-/
@[simp] theorem principalUnitSubOne_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v] :
    principalUnitSubOneOfWithZeroValuation v
        (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) =
      0 := by
  simp [principalUnitSubOneOfWithZeroValuation]

/-- The additive parameter of a product of first principal units is
`(u - 1) + (w - 1) + (u - 1)(w - 1)`.  This is the algebraic input for the
formal identity `log((1 + x)(1 + y)) = log(1 + x) + log(1 + y)`. -/
theorem principalUnitSubOne_mul_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) :
    principalUnitSubOneOfWithZeroValuation v (u * w) =
      principalUnitSubOneOfWithZeroValuation v u +
        principalUnitSubOneOfWithZeroValuation v w +
          principalUnitSubOneOfWithZeroValuation v u *
            principalUnitSubOneOfWithZeroValuation v w := by
  simp [principalUnitSubOneOfWithZeroValuation]
  ring
