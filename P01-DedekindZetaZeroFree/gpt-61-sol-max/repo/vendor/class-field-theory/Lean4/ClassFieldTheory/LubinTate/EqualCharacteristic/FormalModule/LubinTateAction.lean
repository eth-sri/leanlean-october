module

public import Mathlib

public import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Equal-characteristic Lubin--Tate action

This file proves the algebraic identities needed to turn the finite brackets
from `EqualCharacteristicLubinTateEnd` into the action of
`(κ⟦T⟧ / T^n)ˣ` on the `T^n`-division points.
-/

noncomputable section

open scoped PowerSeries LaurentSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]













section
variable {k : Type*} [Semiring k] (a : k⟦X⟧)
include k a
/-- Delete the constant coefficient of a power series and shift all
remaining coefficients down by one place. -/
noncomputable def equalCharacteristicPowerSeriesTail
       :=
  PowerSeries.mk fun i ↦ PowerSeries.coeff (i + 1) a

/-- States the theorem `equalCharacteristicPowerSeriesTail_coeff`. -/
@[simp]
theorem equalCharacteristicPowerSeriesTail_coeff
      (i : ℕ) :
    PowerSeries.coeff i (equalCharacteristicPowerSeriesTail a) =
      PowerSeries.coeff (i + 1) a := by
  simp [equalCharacteristicPowerSeriesTail]

/-- Split a power series into its constant coefficient and shifted tail. -/
theorem equalCharacteristicPowerSeries_eq_X_mul_tail_add_C
      :
    a = PowerSeries.X * equalCharacteristicPowerSeriesTail a +
      PowerSeries.C (PowerSeries.coeff 0 a) := by
  simpa [equalCharacteristicPowerSeriesTail,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      PowerSeries.eq_X_mul_shift_add_const a
end


/-- Product rule for the shifted tail:
`tail(ab) = C(a₀) tail(b) + tail(a)b`. -/
theorem equalCharacteristicPowerSeriesTail_mul
    {k : Type*} [CommRing k] (a b : k⟦X⟧) :
    equalCharacteristicPowerSeriesTail (a * b) =
      PowerSeries.C (PowerSeries.coeff 0 a) *
          equalCharacteristicPowerSeriesTail b +
        equalCharacteristicPowerSeriesTail a * b := by
  apply PowerSeries.X_mul_injective
  have ha := equalCharacteristicPowerSeries_eq_X_mul_tail_add_C a
  have hb := equalCharacteristicPowerSeries_eq_X_mul_tail_add_C b
  have hab := equalCharacteristicPowerSeries_eq_X_mul_tail_add_C (a * b)
  have hcoeff :
      PowerSeries.coeff 0 (a * b) =
        PowerSeries.coeff 0 a * PowerSeries.coeff 0 b := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  calc
    PowerSeries.X * equalCharacteristicPowerSeriesTail (a * b) =
        a * b - PowerSeries.C (PowerSeries.coeff 0 (a * b)) := by
      calc
        _ =
            (PowerSeries.X * equalCharacteristicPowerSeriesTail (a * b) +
                PowerSeries.C (PowerSeries.coeff 0 (a * b))) -
              PowerSeries.C (PowerSeries.coeff 0 (a * b)) := by ring
        _ = a * b - PowerSeries.C (PowerSeries.coeff 0 (a * b)) := by
          rw [← hab]
    _ = a * b - PowerSeries.C
          (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) := by
      rw [hcoeff]
    _ =
        (PowerSeries.X * equalCharacteristicPowerSeriesTail a +
            PowerSeries.C (PowerSeries.coeff 0 a)) * b -
          PowerSeries.C
            (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) := congrArg
        (fun z : k⟦X⟧ ↦
          z * b - PowerSeries.C
            (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b)) ha
    _ = PowerSeries.X * (equalCharacteristicPowerSeriesTail a * b) +
          (PowerSeries.C (PowerSeries.coeff 0 a) * b -
            PowerSeries.C
              (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b)) := by
      ring
    _ = PowerSeries.X * (equalCharacteristicPowerSeriesTail a * b) +
          PowerSeries.X *
            (PowerSeries.C (PowerSeries.coeff 0 a) *
              equalCharacteristicPowerSeriesTail b) := by
      congr 1
      calc
        PowerSeries.C (PowerSeries.coeff 0 a) * b -
            PowerSeries.C
              (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) =
            PowerSeries.C (PowerSeries.coeff 0 a) *
                (PowerSeries.X * equalCharacteristicPowerSeriesTail b +
                  PowerSeries.C (PowerSeries.coeff 0 b)) -
              PowerSeries.C
                (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) := congrArg
            (fun z : k⟦X⟧ ↦
              PowerSeries.C (PowerSeries.coeff 0 a) * z -
                PowerSeries.C
                  (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b)) hb
        _ = PowerSeries.X *
            (PowerSeries.C (PowerSeries.coeff 0 a) *
              equalCharacteristicPowerSeriesTail b) := by
          rw [mul_add,
            ← map_mul PowerSeries.C]
          ring
    _ = PowerSeries.X *
          (PowerSeries.C (PowerSeries.coeff 0 a) *
              equalCharacteristicPowerSeriesTail b +
            equalCharacteristicPowerSeriesTail a * b) := by
      ring









































































































































































































































































































end EqualCharacteristic
end LubinTate

end
