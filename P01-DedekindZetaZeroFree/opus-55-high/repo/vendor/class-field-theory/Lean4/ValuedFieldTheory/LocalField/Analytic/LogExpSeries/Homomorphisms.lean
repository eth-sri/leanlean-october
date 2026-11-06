module

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitLog

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

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

/--
Establishes the identity `principalUnitLogSeriesOfWithZeroValuation v (1 :
(CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) hnK = 0`.
-/
@[simp] theorem principalUnitLogSeries_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogSeriesOfWithZeroValuation v
        (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
        hnK = 0 := by
  simp [principalUnitLogSeriesOfWithZeroValuation]

/-- Product of principal units, rewritten as the `log(1 + z)` argument for
`z = (u - 1) + (w - 1) + (u - 1)(w - 1)`. -/
theorem principalUnitLogSeries_mul_argument_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
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
