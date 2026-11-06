module

public import Mathlib

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitLog

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false
/-!
Packages the convergent logarithm and exponential series as additive and multiplicative
homomorphisms on their natural nonarchimedean domains.
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

section
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
include v
/-- Finite logarithm polynomials of a first principal unit. -/
noncomputable def principalUnitLogPartialSumOfWithZeroValuation
     
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ)  :=
  logOnePlusPartialSumField (principalUnitSubOneOfWithZeroValuation v u) hnK N























/--
Establishes the identity `principalUnitLogSeriesOfWithZeroValuation v (1 :
(CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) hnK = 0`.
-/
@[simp] theorem principalUnitLogSeries_one_ofWithZeroValuation
     
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogSeriesOfWithZeroValuation v
        (1)
        hnK = 0 := by
  simp [principalUnitLogSeriesOfWithZeroValuation]







































































































































































































































































































































/-- Product of principal units, rewritten as the `log(1 + z)` argument for
`z = (u - 1) + (w - 1) + (u - 1)(w - 1)`. -/
theorem principalUnitLogSeries_mul_argument_ofWithZeroValuation
     
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      logOnePlusSeriesFieldOfWithZeroValuation v
        (principalUnitSubOneOfWithZeroValuation v u +
          principalUnitSubOneOfWithZeroValuation v w +
            principalUnitSubOneOfWithZeroValuation v u *
              principalUnitSubOneOfWithZeroValuation v w) hnK := by
  simp [principalUnitLogSeriesOfWithZeroValuation,
    principalUnitSubOne_mul_ofWithZeroValuation]

/-- Finite-logarithm-polynomial version of
`principalUnitLogSeries_mul_argument_ofWithZeroValuation`. -/
theorem principalUnitLogPartialSum_mul_argument_ofWithZeroValuation
     
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) :
    principalUnitLogPartialSumOfWithZeroValuation v (u * w) hnK N =
      logOnePlusPartialSumField
        (principalUnitSubOneOfWithZeroValuation v u +
          principalUnitSubOneOfWithZeroValuation v w +
            principalUnitSubOneOfWithZeroValuation v u *
              principalUnitSubOneOfWithZeroValuation v w) hnK N := by
  simp [principalUnitLogPartialSumOfWithZeroValuation,
    principalUnitSubOne_mul_ofWithZeroValuation]





































































































/-- The finite logarithm polynomials of a first principal unit converge to the
principal-unit logarithm-series value. -/
theorem tendsto_principalUnitLogPartialSum_ofWithZeroValuation
     
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ))) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        principalUnitLogPartialSumOfWithZeroValuation v u hnK N)
      atTop (𝓝 (principalUnitLogSeriesOfWithZeroValuation v u hnK)) := (id (tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one v (principalUnitSubOneOfWithZeroValuation v u) hnK hnval (principalUnitSubOne_val_lt_one_ofWithZeroValuation v u) hcomplete))

















































/-- The sum of two finite principal-unit logarithm polynomials converges to
`Log(u) + Log(w)`. -/
theorem tendsto_principalUnitLogPartialSum_add_ofWithZeroValuation
     
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ))) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
          principalUnitLogPartialSumOfWithZeroValuation v w hnK N)
      atTop
      (𝓝 (principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK)) := by
  let  := Valued.mk' v
  have hu :=
    tendsto_principalUnitLogPartialSum_ofWithZeroValuation
      (v := v) (p := p) u hnK hnval hcomplete
  have hw :=
    tendsto_principalUnitLogPartialSum_ofWithZeroValuation
      (v := v) (p := p) w hnK hnval hcomplete
  exact hu.add hw
end


/-- If two convergent field-valued sequences differ by a sequence converging
to zero, then their limits agree.  This is the topological endpoint used to
turn the formal logarithm product defect into actual additivity of the local
logarithm. -/
theorem eq_of_tendsto_sub_zero
    [TopologicalSpace K] [T2Space K] [ContinuousAdd K] [ContinuousNeg K]
    {f g : ℕ → K} {a b : K}
    (hf : Tendsto f atTop (𝓝 a))
    (hg : Tendsto g atTop (𝓝 b))
    (hsub : Tendsto (fun n => f n - g n) atTop (𝓝 0)) :
    a = b := by
  have hfg  :=
    hsub.add hg
  have hf' : Tendsto f atTop (𝓝 b) := by
    simpa [sub_eq_add_neg, add_assoc] using hfg
  exact tendsto_nhds_unique hf hf'

/-- The principal-unit logarithm product defect is the same as the field-level
defect for the two additive parameters `u - 1` and `w - 1`. -/
theorem principalUnitLogPartialSum_product_defect_eq_field_defect_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) :
    principalUnitLogPartialSumOfWithZeroValuation v (u * w) hnK N -
        (principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
          principalUnitLogPartialSumOfWithZeroValuation v w hnK N) =
      logOnePlusPartialSumField
          (principalUnitSubOneOfWithZeroValuation v u +
            principalUnitSubOneOfWithZeroValuation v w +
              principalUnitSubOneOfWithZeroValuation v u *
                principalUnitSubOneOfWithZeroValuation v w) hnK N -
        (logOnePlusPartialSumField
            (principalUnitSubOneOfWithZeroValuation v u) hnK N +
          logOnePlusPartialSumField
            (principalUnitSubOneOfWithZeroValuation v w) hnK N) := by
  rw [principalUnitLogPartialSum_mul_argument_ofWithZeroValuation]
  simp [principalUnitLogPartialSumOfWithZeroValuation]

section
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ))) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
include v p u w hnK hnval
/-- Principal-unit logarithm additivity reduced to the one remaining analytic
bridge: the difference between the product logarithm partial sums and the
sum of the two logarithm partial sums tends to zero.  The formal identity
proved above supplies the coefficient cancellation for this defect; this
lemma records the exact topological endpoint needed by the field-unit logarithm theorem. -/
theorem principalUnitLogSeries_mul_eq_add_of_tendsto_defect_ofWithZeroValuation
     
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto
        (fun N : ℕ =>
          principalUnitLogPartialSumOfWithZeroValuation v (u * w) hnK N -
            (principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
              principalUnitLogPartialSumOfWithZeroValuation v w hnK N))
        atTop (𝓝 (0))) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK := by
  let  := Valued.mk' v
  have hprod :=
    tendsto_principalUnitLogPartialSum_ofWithZeroValuation
      (v := v) (p := p) (u * w) hnK hnval hcomplete
  have hadd :=
    tendsto_principalUnitLogPartialSum_add_ofWithZeroValuation
      (v := v) (p := p) u w hnK hnval hcomplete
  apply eq_of_tendsto_sub_zero <;> assumption

/-- Field-level version of
`principalUnitLogSeries_mul_eq_add_of_tendsto_defect_ofWithZeroValuation`.
After this reduction, the remaining analytic work for the field-unit logarithm theorem is to
prove that the displayed field-level defect tends to zero from the formal
coefficient identity. -/
theorem principalUnitLogSeries_mul_eq_add_of_tendsto_field_defect_ofWithZeroValuation
     
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto
        (fun N : ℕ =>
          logOnePlusPartialSumField
              (principalUnitSubOneOfWithZeroValuation v u +
                principalUnitSubOneOfWithZeroValuation v w +
                  principalUnitSubOneOfWithZeroValuation v u *
                    principalUnitSubOneOfWithZeroValuation v w) hnK N -
            (logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u) hnK N +
              logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v w) hnK N))
        atTop (𝓝 (0))) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK := by
  apply principalUnitLogSeries_mul_eq_add_of_tendsto_defect_ofWithZeroValuation
    (v := v) (p := p) u w hnK hnval hcomplete
  let  := Valued.mk' v
  simpa [principalUnitLogPartialSum_product_defect_eq_field_defect_ofWithZeroValuation
    (v := v) u w hnK] using hdefect
end


section
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ))) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
include v p hnK hnval
/-- Principal-unit logarithm as a multiplicative homomorphism, conditional only
on the remaining field-level defect convergence.  The codomain is written as
`Multiplicative K`, so multiplication there is addition in the local field. -/
noncomputable def principalUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuation
     
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0))) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 →*
      Multiplicative K where
  toFun u := Multiplicative.ofAdd
    (principalUnitLogSeriesOfWithZeroValuation v u hnK)
  map_one' := by
    simp
  map_mul' u w := by
    change
      Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK) =
        Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v u hnK +
            principalUnitLogSeriesOfWithZeroValuation v w hnK)
    rw [principalUnitLogSeries_mul_eq_add_of_tendsto_field_defect_ofWithZeroValuation
      (v := v) (p := p) u w hnK hnval hcomplete (hdefect u w)]

/--
Establishes the identity `Multiplicative.toAdd
(principalUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuation (v := v) (p := p) hnK hnval
hcomplete hdefect u) = principalUnitLogSeriesOfWithZeroValuation v u hnK`.
-/
@[simp] theorem principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation
     
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0)))
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) :
    Multiplicative.toAdd
        (principalUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuation
          (v := v) (p := p) hnK hnval hcomplete hdefect u) =
      principalUnitLogSeriesOfWithZeroValuation v u hnK := rfl
end


section
variable (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A)
include F A φ
/-- A homomorphism on first principal units extends to the three-factor
decomposition of `Kˣ` by killing the Teichmuller root factor and the
uniformizer factor.  This is the algebraic extension shape used in the field-unit logarithm theorem after the principal-unit logarithm has been proved additive. -/
noncomputable def fieldUnitDecompositionLogHomOfPrincipalUnitHom
      :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F →*
      Multiplicative A where
  toFun z := φ z.1.2
  map_one' := by
    simp
  map_mul' z w := by
    simp

/--
The defining evaluation formula for `fieldUnitDecompositionLogHomOfPrincipalUnitHom` is
`fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ z = φ z.1.2`.
-/
@[simp] theorem fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply
     
    (z : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ z = φ z.1.2 :=
  rfl
end














































section
variable (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (e : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A)
include F A e φ
/-- A field-unit logarithm homomorphism obtained from a chosen the uniformizer–residue–principal-unit decomposition
three-factor decomposition and a principal-unit logarithm homomorphism. -/
noncomputable def fieldUnitLogHomOfPrincipalUnitHom
       :=
  (fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ).comp
    e.symm.toMonoidHom

/--
The defining evaluation formula for `fieldUnitLogHomOfPrincipalUnitHom` is
`fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = φ ((e.symm x).1.2)`.
-/
@[simp] theorem fieldUnitLogHomOfPrincipalUnitHom_apply
      (x : Kˣ) :
    fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x =
      φ ((e.symm x).1.2) :=
  rfl
end

















































































































































































































































































































































































































































































end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
