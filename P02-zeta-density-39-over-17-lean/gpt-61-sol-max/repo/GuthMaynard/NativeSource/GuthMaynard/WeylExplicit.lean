module
public import GuthMaynard.WeylExplicit
public import GuthMaynard.NativeSource.GuthMaynard.Weyl
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Complex Finset Set
open scoped BigOperators

namespace GuthMaynard.NativeMoment

-- Share the classical exponential-sum implementation.
export RiemannZeta.GuthMaynard (
  classicalWeylShiftLength
  classicalWeylShiftLength_spec
  logarithmic_weyl_AB_process_simple
  simpleLogarithmicCorrelationBound
)

/-!
# Explicit Weyl exponent bounds

This module simplifies the finite A-after-B estimate to the classical
`(1/6, 2/3)` exponent scale on medium logarithmic blocks.  All constants and
shift choices are explicit and the final prefix estimate has no analytic
premise.
-/

/-- Slack-bearing form of the uniform logarithmic correlation estimate.
The factor `X` records the precise amount by which the physical block may
cross the ideal Weyl boundary `A ^ 2 ≤ Y ^ 3`. -/
theorem simpleLogarithmicCorrelationBound_le_four_hundred_mul
    (Y X : Real) (A H : Nat) (hY : 1 ≤ Y) (hX : 1 ≤ X) (hA : 0 < A)
    (hHY : (H : Real) * Y ≤ A)
    (hAY : (A : Real) ^ 2 ≤ X * Y ^ 3) :
    simpleLogarithmicCorrelationBound (Y ^ 3) A A H ≤ 400 * X * Y := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hAreal : 0 < (A : Real) := Nat.cast_pos.mpr hA
  let q : Real := Y ^ 3 / (8 * (A : Real) ^ 3)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqH_le : q * H ≤ (Y / (A : Real)) ^ 2 := by
    dsimp only [q]
    rw [show Y ^ 3 / (8 * (A : Real) ^ 3) * (H : Real) =
      (Y ^ 3 * H) / (8 * (A : Real) ^ 3) by ring]
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < 8 * (A : Real) ^ 3)
      (by positivity : 0 < (A : Real) ^ 2)]
    calc
      Y ^ 3 * (H : Real) * (A : Real) ^ 2 =
          ((H : Real) * Y) * (Y ^ 2 * (A : Real) ^ 2) := by ring
      _ ≤ (A : Real) * (Y ^ 2 * (A : Real) ^ 2) :=
        mul_le_mul_of_nonneg_right hHY (mul_nonneg (pow_nonneg hYpos.le 2)
          (pow_nonneg hAreal.le 2))
      _ ≤ 8 * (A : Real) * (Y ^ 2 * (A : Real) ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith
        · positivity
      _ = Y ^ 2 * (8 * (A : Real) ^ 3) := by ring
  have hsqrtHigh : Real.sqrt (q * H) ≤ Y / (A : Real) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hqH_le⟩
  have hfirst : (A : Real) * Real.sqrt (q * H) ≤ Y := by
    calc
      (A : Real) * Real.sqrt (q * H) ≤ (A : Real) * (Y / (A : Real)) :=
        mul_le_mul_of_nonneg_left hsqrtHigh hAreal.le
      _ = Y := by field_simp
  have hY3_le_Y4 : Y ^ 3 ≤ Y ^ 4 := by
    have := mul_le_mul_of_nonneg_left hY (pow_nonneg hYpos.le 3)
    nlinarith
  have hX_le_X2 : X ≤ X ^ 2 := by nlinarith
  have hA_le_XY2 : (A : Real) ≤ X * Y ^ 2 := by
    have hsquares : (A : Real) ^ 2 ≤ (X * Y ^ 2) ^ 2 := by
      calc
        (A : Real) ^ 2 ≤ X * Y ^ 3 := hAY
        _ ≤ X * Y ^ 4 := mul_le_mul_of_nonneg_left hY3_le_Y4 hXpos.le
        _ ≤ X ^ 2 * Y ^ 4 := mul_le_mul_of_nonneg_right hX_le_X2
          (pow_nonneg hYpos.le 4)
        _ = (X * Y ^ 2) ^ 2 := by ring
    nlinarith [sq_nonneg ((A : Real) - X * Y ^ 2)]
  have hA3_le : (A : Real) ^ 3 ≤ X ^ 2 * Y ^ 5 := by
    calc
      (A : Real) ^ 3 = (A : Real) ^ 2 * A := by ring
      _ ≤ (X * Y ^ 3) * (X * Y ^ 2) :=
        mul_le_mul hAY hA_le_XY2 hAreal.le (mul_nonneg hXpos.le (pow_nonneg hYpos.le 3))
      _ = X ^ 2 * Y ^ 5 := by ring
  have hsquareLow : (1 / (3 * X * Y)) ^ 2 ≤ q := by
    dsimp only [q]
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < (3 * X * Y) ^ 2)
      (by positivity : 0 < 8 * (A : Real) ^ 3)]
    nlinarith [hA3_le, mul_nonneg (pow_nonneg hXpos.le 2) (pow_nonneg hYpos.le 5)]
  have hsqrtLow : 1 / (3 * X * Y) ≤ Real.sqrt q :=
    Real.le_sqrt_of_sq_le hsquareLow
  have hsecond : 1 / Real.sqrt q ≤ 3 * X * Y := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hq)]
    have hmul := mul_le_mul_of_nonneg_left hsqrtLow
      (by positivity : 0 ≤ 3 * X * Y)
    field_simp [hXpos.ne', hYpos.ne'] at hmul
    nlinarith
  unfold simpleLogarithmicCorrelationBound
  dsimp only
  change 100 * ((A : Real) * Real.sqrt (q * H) + 1 / Real.sqrt q) ≤
    400 * X * Y
  nlinarith [mul_pos hXpos hYpos]

/-- Uniform prefix Weyl estimate with an explicit multiplicative boundary
slack.  This is the source-faithful form needed after the floored reflected
cutoff, where the ideal relation `A ^ 2 ≤ Y ^ 3` is enlarged by a known
power of the ambient height. -/
theorem logarithmic_weyl_exponent_pair_prefix_with_slack
    (Y X : Real) (A N : Nat) (hY : 1 ≤ Y) (hX : 1 ≤ X) (hA : 0 < A)
    (hYA : Y ≤ A) (hAY : (A : Real) ^ 2 ≤ X * Y ^ 3) (hNA : N ≤ A) :
    ‖logarithmicSum (Y ^ 3) A (A + N)‖ ≤
      30 * Real.sqrt (X * (A : Real) * Y) := by
  obtain ⟨hH, hHle, hHY, hAH⟩ := classicalWeylShiftLength_spec Y A hY hA hYA
  let H := classicalWeylShiftLength Y A
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hAreal : 0 < (A : Real) := Nat.cast_pos.mpr hA
  have hHreal : 0 < (H : Real) := Nat.cast_pos.mpr hH
  have hNreal : (N : Real) ≤ A := by exact_mod_cast hNA
  have hsqrtSq : Real.sqrt (X * (A : Real) * Y) ^ 2 = X * (A : Real) * Y :=
    Real.sq_sqrt (by positivity)
  by_cases hHN : H ≤ N
  · have hsmall : Y ^ 3 * (H : Real) / (8 * (A : Real) ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 8 * (A : Real) ^ 3)]
      calc
        Y ^ 3 * (H : Real) = ((H : Real) * Y) * Y ^ 2 := by ring
        _ ≤ (A : Real) * Y ^ 2 :=
          mul_le_mul_of_nonneg_right hHY (pow_nonneg hYpos.le 2)
        _ ≤ (A : Real) * (A : Real) ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · nlinarith
          · exact hAreal.le
        _ ≤ 8 * (A : Real) ^ 3 := by nlinarith [pow_pos hAreal 3]
    have hab := logarithmic_weyl_AB_process_simple
      (Y ^ 3) A N H (pow_pos hYpos 3) hAreal hHN hNreal hsmall
    rw [integerLogarithmicSum_eq] at hab
    have hcA := simpleLogarithmicCorrelationBound_le_four_hundred_mul
      Y X A H hY hX hA hHY hAY
    have hcN : simpleLogarithmicCorrelationBound (Y ^ 3) A N H ≤
        400 * X * Y := by
      exact (show simpleLogarithmicCorrelationBound (Y ^ 3) A N H ≤
          simpleLogarithmicCorrelationBound (Y ^ 3) A A H by
        unfold simpleLogarithmicCorrelationBound
        dsimp only
        apply mul_le_mul_of_nonneg_left
        · let s := Real.sqrt (Y ^ 3 / (8 * (A : Real) ^ 3) * (H : Real))
          have hm : (N : Real) * s ≤ (A : Real) * s :=
            mul_le_mul_of_nonneg_right hNreal (Real.sqrt_nonneg _)
          dsimp only [s] at hm
          linarith
        · norm_num).trans hcA
    have hab' :
        (H : Real) ^ 2 * ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 ≤
          (((N + H : Nat) : Real) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * X * Y))) := by
      exact hab.trans (by gcongr)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at hab'
    have houter : (N : Real) + H ≤ 2 * A := by
      have hHcast : (H : Real) ≤ A := by exact_mod_cast hHle
      nlinarith
    have hinner : (H : Real) * N + (H : Real) ^ 2 * (400 * X * Y) ≤
        402 * X * (H : Real) ^ 2 * Y := by
      have hHA : (H : Real) * N ≤ 2 * (H : Real) ^ 2 * Y := by
        have hNAH := hNreal.trans hAH
        have := mul_le_mul_of_nonneg_left hNAH (Nat.cast_nonneg H)
        nlinarith
      have hFirst : 2 * (H : Real) ^ 2 * Y ≤
          2 * X * (H : Real) ^ 2 * Y := by
        have hNonneg : 0 ≤ 2 * (H : Real) ^ 2 * Y := by positivity
        nlinarith
      nlinarith [mul_nonneg (sq_nonneg (H : Real)) hYpos.le]
    have hrightNonneg : 0 ≤
        (H : Real) * N + (H : Real) ^ 2 * (400 * X * Y) := by positivity
    have hbound :
        (((N : Real) + H) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * X * Y))) ≤
          900 * (H : Real) ^ 2 * X * A * Y := by
      calc
        ((N : Real) + H) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * X * Y)) ≤
            (2 * A) * ((H : Real) * N +
              (H : Real) ^ 2 * (400 * X * Y)) :=
          mul_le_mul_of_nonneg_right houter hrightNonneg
        _ ≤ (2 * A) * (402 * X * (H : Real) ^ 2 * Y) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ 900 * (H : Real) ^ 2 * X * A * Y := by
          have hnonneg := mul_nonneg
            (mul_nonneg (mul_nonneg (sq_nonneg (H : Real)) hXpos.le) hAreal.le)
            hYpos.le
          nlinarith
    have hsq : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 ≤
        900 * (X * (A : Real) * Y) := by
      have := hab'.trans hbound
      nlinarith [sq_pos_of_pos hHreal]
    nlinarith [norm_nonneg (logarithmicSum (Y ^ 3) A (A + N)),
      Real.sqrt_nonneg (X * (A : Real) * Y)]
  · have hNH : N < H := Nat.lt_of_not_ge hHN
    have htrivial := norm_logarithmicSum_le_length (Y ^ 3) A (A + N)
    have hlength : (A + N - A : Nat) = N := by omega
    rw [hlength] at htrivial
    have hHYsq : ((H : Real) * Y) ^ 2 ≤ (A : Real) ^ 2 := by
      nlinarith [sq_nonneg ((A : Real) - (H : Real) * Y)]
    have hHsqY : (H : Real) ^ 2 ≤ X * Y := by
      have hmul : Y ^ 2 * (H : Real) ^ 2 ≤ Y ^ 2 * (X * Y) := by
        calc
          Y ^ 2 * (H : Real) ^ 2 = ((H : Real) * Y) ^ 2 := by ring
          _ ≤ (A : Real) ^ 2 := hHYsq
          _ ≤ X * Y ^ 3 := hAY
          _ = Y ^ 2 * (X * Y) := by ring
      by_contra hnot
      have hlt : X * Y < (H : Real) ^ 2 := lt_of_not_ge hnot
      have hcontra := mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hYpos)
      exact (not_lt_of_ge hmul) hcontra
    have hHsqXAY : (H : Real) ^ 2 ≤ X * (A : Real) * Y := by
      calc
        (H : Real) ^ 2 ≤ X * Y := hHsqY
        _ ≤ X * (A : Real) * Y := by
          have hAone : (1 : Real) ≤ A := by exact_mod_cast hA
          nlinarith [mul_pos hXpos hYpos]
    have hNlt : (N : Real) < H := by exact_mod_cast hNH
    have hnorm : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ≤ H :=
      htrivial.trans hNlt.le
    have hnormSq : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 ≤
        X * (A : Real) * Y := by
      nlinarith [norm_nonneg (logarithmicSum (Y ^ 3) A (A + N))]
    have hsqrtBound : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ≤
        Real.sqrt (X * (A : Real) * Y) := Real.le_sqrt_of_sq_le hnormSq
    calc
      ‖logarithmicSum (Y ^ 3) A (A + N)‖ ≤
          Real.sqrt (X * (A : Real) * Y) := hsqrtBound
      _ ≤ 30 * Real.sqrt (X * (A : Real) * Y) := by
        nlinarith [Real.sqrt_nonneg (X * (A : Real) * Y)]

end GuthMaynard.NativeMoment
