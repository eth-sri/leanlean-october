module
public import GuthMaynard.Weyl
public import Mathlib.Analysis.Real.Pi.Bounds
public import GuthMaynard.NativeSource.GuthMaynard.WeylExplicit
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Finset Set

namespace RiemannZeta.GuthMaynard

/-!
# Explicit Weyl exponent bounds

This module simplifies the finite A-after-B estimate to the classical
`(1/6, 2/3)` exponent scale on medium logarithmic blocks.  All constants and
shift choices are explicit and the final prefix estimate has no analytic
premise.
-/

export GuthMaynard.NativeMoment (vdc_product_bound classicalWeylShiftLength_spec logarithmicCorrelationBound_le_simple logarithmicCorrelationBound_le_uniform logarithmic_weyl_AB_process_simple simpleLogarithmicCorrelationBound classicalWeylShiftLength)

theorem simpleLogarithmicCorrelationBound_le_four_hundred
    (Y : Real) (A H : Nat) (hY : 1 <= Y) (hA : 0 < A)
    (hHY : (H : Real) * Y <= A) (hAY : (A : Real) ^ 2 <= Y ^ 3) :
    simpleLogarithmicCorrelationBound (Y ^ 3) A A H <= 400 * Y := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  pm_4846
  have hA_le_Y_sq : (A : Real) <= Y ^ 2 := by
    have hY3_le_Y4 : Y ^ 3 <= Y ^ 4 := by
      pm_8405
    nlinarith [sq_nonneg ((A : Real) - Y ^ 2)]
  have hqH_le : q * H <= (Y / (A : Real)) ^ 2 := by
    pm_4845
    calc
      Y ^ 3 * (H : Real) * (A : Real) ^ 2 =
          ((H : Real) * Y) * (Y ^ 2 * (A : Real) ^ 2) := by ring
      _ <= (A : Real) * (Y ^ 2 * (A : Real) ^ 2) :=
        mul_le_mul_of_nonneg_right hHY (mul_nonneg (pow_nonneg hYpos.le 2)
          (pow_nonneg hAreal.le 2))
      _ <= 8 * (A : Real) * (Y ^ 2 * (A : Real) ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith
        · positivity
      _ = Y ^ 2 * (8 * (A : Real) ^ 3) := by ring
  have hsqrtHigh : Real.sqrt (q * H) <= Y / (A : Real) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hqH_le⟩
  have hfirst : (A : Real) * Real.sqrt (q * H) <= Y := by
    calc
      (A : Real) * Real.sqrt (q * H) <= (A : Real) * (Y / (A : Real)) :=
        mul_le_mul_of_nonneg_left hsqrtHigh hAreal.le
      _ = Y := by field_simp
  have hA3_le_Y5 : (A : Real) ^ 3 <= Y ^ 5 := by
    calc
      (A : Real) ^ 3 = (A : Real) ^ 2 * A := by ring
      _ <= Y ^ 3 * Y ^ 2 := mul_le_mul hAY hA_le_Y_sq
        (Nat.cast_nonneg A) (pow_nonneg hYpos.le 3)
      _ = Y ^ 5 := by ring
  have hsquareLow : (1 / (3 * Y)) ^ 2 <= q := by
    dsimp only [q]
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < (3 * Y) ^ 2)
      (by positivity : 0 < 8 * (A : Real) ^ 3)]
    nlinarith [hA3_le_Y5, pow_nonneg hYpos.le 5]
  have hsqrtLow : 1 / (3 * Y) <= Real.sqrt q :=
    Real.le_sqrt_of_sq_le hsquareLow
  have hsecond : 1 / Real.sqrt q <= 3 * Y := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hq)]
    have hmul := mul_le_mul_of_nonneg_left hsqrtLow (by positivity : 0 <= 3 * Y)
    field_simp [hYpos.ne'] at hmul
    nlinarith
  unfold simpleLogarithmicCorrelationBound
  dsimp only
  change 100 * ((A : Real) * Real.sqrt (q * H) + 1 / Real.sqrt q) <= 400 * Y
  nlinarith

/-- Uniform prefix form of the `(1/6, 2/3)` bound, needed for Abel
summation of the critical-line weight. -/
theorem logarithmic_weyl_exponent_pair_prefix
    (Y : Real) (A N : Nat) (hY : 1 <= Y) (hA : 0 < A)
    (hYA : Y <= A) (hAY : (A : Real) ^ 2 <= Y ^ 3) (hNA : N <= A) :
    ‖logarithmicSum (Y ^ 3) A (A + N)‖ <=
      30 * Real.sqrt ((A : Real) * Y) := by
  pm_4849
  pm_1060
  have hNreal : (N : Real) <= A := by exact_mod_cast hNA
  have hsqrtSq : Real.sqrt ((A : Real) * Y) ^ 2 = (A : Real) * Y :=
    Real.sq_sqrt (mul_nonneg hAreal.le hYpos.le)
  have hsqrtNonneg : 0 <= Real.sqrt ((A : Real) * Y) := Real.sqrt_nonneg _
  by_cases hHN : H <= N
  · have hsmall : Y ^ 3 * (H : Real) / (8 * (A : Real) ^ 3) <= 1 := by
      pm_5885
      calc
        Y ^ 3 * (H : Real) = ((H : Real) * Y) * Y ^ 2 := by ring
        _ <= (A : Real) * Y ^ 2 :=
          mul_le_mul_of_nonneg_right hHY (pow_nonneg hYpos.le 2)
        _ <= (A : Real) * (A : Real) ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · nlinarith
          · exact hAreal.le
        _ <= 8 * (A : Real) ^ 3 := by nlinarith [pow_pos hAreal 3]
    pm_956
    have hcA := simpleLogarithmicCorrelationBound_le_four_hundred
      Y A H hY hA hHY hAY
    have hcN : simpleLogarithmicCorrelationBound (Y ^ 3) A N H <= 400 * Y := by
      exact (show simpleLogarithmicCorrelationBound (Y ^ 3) A N H <=
          simpleLogarithmicCorrelationBound (Y ^ 3) A A H by
        unfold simpleLogarithmicCorrelationBound
        dsimp only
        apply mul_le_mul_of_nonneg_left
        · let s := Real.sqrt (Y ^ 3 / (8 * (A : Real) ^ 3) * (H : Real))
          have hm : (N : Real) * s <= (A : Real) * s :=
            mul_le_mul_of_nonneg_right hNreal (Real.sqrt_nonneg _)
          dsimp only [s] at hm
          linarith
        · norm_num).trans hcA
    have hab' :
        (H : Real) ^ 2 * ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 <=
          (((N + H : Nat) : Real) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * Y))) := by
      exact hab.trans (by gcongr)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at hab'
    have houter : (N : Real) + H <= 2 * A := by
      have hHcast : (H : Real) <= A := by exact_mod_cast hHle
      nlinarith
    have hinner : (H : Real) * N + (H : Real) ^ 2 * (400 * Y) <=
        402 * (H : Real) ^ 2 * Y := by
      have hHA : (H : Real) * N <= 2 * (H : Real) ^ 2 * Y := by
        pm_7290
      pm_7566
    have hrightNonneg : 0 <=
        (H : Real) * N + (H : Real) ^ 2 * (400 * Y) := by positivity
    have hbound :
        (((N : Real) + H) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * Y))) <=
          900 * (H : Real) ^ 2 * A * Y := by
      calc
        ((N : Real) + H) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * Y)) <=
            (2 * A) * ((H : Real) * N + (H : Real) ^ 2 * (400 * Y)) :=
          mul_le_mul_of_nonneg_right houter hrightNonneg
        _ <= (2 * A) * (402 * (H : Real) ^ 2 * Y) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ <= 900 * (H : Real) ^ 2 * A * Y := by
          have hnonneg := mul_nonneg (mul_nonneg (sq_nonneg (H : Real)) hAreal.le) hYpos.le
          nlinarith
    have hsq : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 <=
        900 * (A : Real) * Y := by
      have := hab'.trans hbound
      nlinarith [sq_pos_of_pos hHreal]
    pm_4847
  · have hNH : N < H := Nat.lt_of_not_ge hHN
    pm_4848
    have hHYsq : ((H : Real) * Y) ^ 2 <= (A : Real) ^ 2 := by
      pm_6097
    have hHsqY : (H : Real) ^ 2 <= Y := by
      have hmul : Y ^ 2 * (H : Real) ^ 2 <= Y ^ 2 * Y := by
        calc
          Y ^ 2 * (H : Real) ^ 2 = ((H : Real) * Y) ^ 2 := by ring
          _ <= (A : Real) ^ 2 := hHYsq
          _ <= Y ^ 3 := hAY
          _ = Y ^ 2 * Y := by ring
      by_contra hnot
      have hlt : Y < (H : Real) ^ 2 := lt_of_not_ge hnot
      pm_7019
    have hHsqAY : (H : Real) ^ 2 <= (A : Real) * Y := by
      calc
        (H : Real) ^ 2 <= Y := hHsqY
        _ <= (A : Real) * Y := by
          have hAone : (1 : Real) <= A := by exact_mod_cast hA
          nlinarith
    pm_7291
    have hnorm : ‖logarithmicSum (Y ^ 3) A (A + N)‖ <= H := htrivial.trans hNlt.le
    have hnormSq : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 <= (A : Real) * Y := by
      pm_4847
    pm_4847

end RiemannZeta.GuthMaynard
