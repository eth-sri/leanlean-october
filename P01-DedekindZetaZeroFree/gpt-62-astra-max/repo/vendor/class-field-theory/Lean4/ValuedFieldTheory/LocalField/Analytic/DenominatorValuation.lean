module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Valuations of natural-number denominators

For a complete discrete valuation with value group `WithZero (Multiplicative ℤ)`
and finite residue field, this file constructs the ramification index
`e = v_K(p)` from the valuation itself.  In mixed characteristic it then proves
the natural-number valuation formula used in the logarithm and exponential theorems.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

variable {K : Type u} [Field K]

/-- The full ordered group structure whose ordered-monoid parent is the
canonical one used by `Valuation` on `ℤᵐ⁰`. -/
@[reducible] def coherentWithZeroMultiplicativeIntGroup :
    LinearOrderedCommGroupWithZero
      (WithZero (Multiplicative ℤ)) where
  __ :=
    (inferInstance :
      LinearOrderedCommMonoidWithZero
        (WithZero (Multiplicative ℤ)))
  __ :=
    (inferInstance :
      CommGroupWithZero
        (WithZero (Multiplicative ℤ)))

section

variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]

/-- Package a standard `ℤᵐ⁰`-valued complete discrete valuation with finite
residue field as a local field. -/
def ofWithZeroValuation :
    LocalField.{u, 0} K where
  toCompleteDVF :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      instValueGroup := coherentWithZeroMultiplicativeIntGroup
      valuation := v
      instCompleteDiscrete := inferInstance }
  residueFinite := by
    infer_instance

/-- The ramification index `e = v_K(p)` of a standard mixed-characteristic
local field, obtained from the exponent of the value of its residue
characteristic `p`. -/
def ramificationIndexOfWithZeroValuation [CharZero K] : ℕ :=
  Int.toNat
    (-WithZero.log
      (v ((ofWithZeroValuation v).residueCharacteristic : K)))

/-- The natural ramification index recovers the normalized integer valuation
of the residue characteristic. -/
theorem ramificationIndexOfWithZeroValuation_intCast [CharZero K] :
    (ramificationIndexOfWithZeroValuation v : ℤ) =
      -WithZero.log
        (v ((ofWithZeroValuation v).residueCharacteristic : K)) := by
  let F := ofWithZeroValuation v
  have hlogneg :
      WithZero.log (v (F.residueCharacteristic : K)) < (0 : ℤ) := by
    have hloglt :
        WithZero.log (v (F.residueCharacteristic : K)) <
          WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.log_lt_log ((_root_.Valuation.ne_zero_iff v).2 F.natCast_residueCharacteristic_ne_zero_of_charZero) one_ne_zero]
      exact F.valuation_natCast_residueCharacteristic_lt_one
    simpa using hloglt
  simpa [ramificationIndexOfWithZeroValuation] using
    Int.toNat_of_nonneg ((neg_pos.mpr hlogneg).le)

/-- The ramification index of a mixed-characteristic local field is positive. -/
theorem ramificationIndexOfWithZeroValuation_pos [CharZero K] :
    0 < ramificationIndexOfWithZeroValuation v := by
  let F := ofWithZeroValuation v
  have hlogneg :
      WithZero.log (v (F.residueCharacteristic : K)) < (0 : ℤ) := by
    have hloglt :
        WithZero.log (v (F.residueCharacteristic : K)) <
          WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.log_lt_log ((_root_.Valuation.ne_zero_iff v).2 F.natCast_residueCharacteristic_ne_zero_of_charZero) one_ne_zero]
      exact F.valuation_natCast_residueCharacteristic_lt_one
    simpa using hloglt
  have heInt :
      (0 : ℤ) < (ramificationIndexOfWithZeroValuation v : ℤ) := by
    rw [ramificationIndexOfWithZeroValuation_intCast v]
    exact neg_pos.mpr hlogneg
  exact_mod_cast heInt

/-- The value of the residue characteristic is `exp (-e)`, where `e` is the
ramification index constructed from the valuation. -/
theorem valuation_residueCharacteristic_eq_exp_neg_ramificationIndex [CharZero K] :
    v ((ofWithZeroValuation v).residueCharacteristic : K) =
      WithZero.exp (-(ramificationIndexOfWithZeroValuation v : ℤ)) := by
  let F := ofWithZeroValuation v
  simpa [ramificationIndexOfWithZeroValuation_intCast v] using (WithZero.exp_log (by simpa [F] using ((_root_.Valuation.ne_zero_iff v).2 F.natCast_residueCharacteristic_ne_zero_of_charZero))).symm

end

/-- A nonzero natural number has valuation equal to the value of its
residue-characteristic power.  This is the denominator formula needed for the
logarithm and exponential estimates in the logarithm and exponential estimates. -/
theorem valuation_natCast_eq_exp_neg_ramificationIndex_mul_padicValNat
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (m : ℕ) (hm : m ≠ 0) :
    v (m : K) =
      WithZero.exp
        (-((ramificationIndexOfWithZeroValuation v : ℤ) *
          (padicValNat (ofWithZeroValuation v).residueCharacteristic m : ℤ))) := by
  let F := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let e := ramificationIndexOfWithZeroValuation v
  let k := padicValNat p m
  let a := m / p ^ k
  let : Fact p.Prime := by
    infer_instance
  have hpow : p ^ k ∣ m := pow_padicValNat_dvd
  have hmfac : p ^ k * a = m := Nat.mul_div_cancel' hpow
  have ha : ¬ p ∣ a := by
    intro hpa
    have hnot : ¬ p ^ (k + 1) ∣ m := by
      simpa [k] using
        (pow_succ_padicValNat_not_dvd hm)
    apply hnot
    rcases hpa with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    calc
      m = p ^ k * a := hmfac.symm
      _ = p ^ k * (p * b) := by rw [hb]
      _ = p ^ (k + 1) * b := by ring
  have hpVal :
      v (p : K) = WithZero.exp (-(e : ℤ)) := by
    simpa [F, p, e] using
      valuation_residueCharacteristic_eq_exp_neg_ramificationIndex v
  have haVal : v (a : K) = 1 := by
    exact F.valuation_natCast_eq_one_of_not_residueCharacteristic_dvd ha
  have hmK : (m : K) = (p : K) ^ k * (a : K) := by
    exact_mod_cast hmfac.symm
  calc
    v (m : K) = v ((p : K) ^ k * (a : K)) := by rw [hmK]
    _ = v (p : K) ^ k * v (a : K) := by simp
    _ = WithZero.exp (-(e : ℤ)) ^ k := by rw [hpVal, haVal, mul_one]
    _ = WithZero.exp (k • (-(e : ℤ))) := by
      rfl
    _ = WithZero.exp (-((e : ℤ) * (k : ℤ))) := by
      simp [mul_comm]
    _ = WithZero.exp
        (-((ramificationIndexOfWithZeroValuation v : ℤ) *
          (padicValNat (ofWithZeroValuation v).residueCharacteristic m : ℤ))) := rfl

/-- Successor form of the natural-number valuation formula.  Unlike the main
formula, this needs no explicit nonzero hypothesis. -/
theorem valuation_natCast_succ_eq_exp_neg_ramificationIndex_mul_padicValNat
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (m : ℕ) :
    v ((m + 1 : ℕ) : K) =
      WithZero.exp
        (-((ramificationIndexOfWithZeroValuation v : ℤ) *
          (padicValNat
            (ofWithZeroValuation v).residueCharacteristic (m + 1) : ℤ))) :=
  valuation_natCast_eq_exp_neg_ramificationIndex_mul_padicValNat
    v (m + 1) (Nat.succ_ne_zero m)

/-- Factorial form of the natural-number valuation formula, used by the
exponential series in the deep exponential–logarithm equivalence. -/
theorem valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (m : ℕ) :
    v ((m.factorial : ℕ) : K) =
      WithZero.exp
        (-((ramificationIndexOfWithZeroValuation v : ℤ) *
          (padicValNat
            (ofWithZeroValuation v).residueCharacteristic m.factorial : ℤ))) :=
  valuation_natCast_eq_exp_neg_ramificationIndex_mul_padicValNat
    v m.factorial (Nat.factorial_ne_zero m)

end LocalField
end LocalFieldTheory.DiscreteValuationField

end
