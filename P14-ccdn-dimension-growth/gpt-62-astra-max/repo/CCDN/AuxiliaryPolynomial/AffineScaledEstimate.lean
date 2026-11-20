/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
public import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary

/-! Normalizing the scaled model at its scaling prime cancels the excess projective box exponent. -/

@[expose] public section
namespace CCDN
noncomputable section

section

variable (n d : ℕ)

/-- The universal degree scale and the affine box power. -/
abbrev auxDegreeScale : ℝ := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
abbrev affineBoxPower (B : ℝ) : ℝ := B ^ (1 / degreeRoot n d)

end

variable {n d : ℕ} (hd : 0 < d) {p B : ℝ}

include hd in
private lemma degreeRoot_one_le : 1 ≤ degreeRoot n d :=
  Real.one_le_rpow (by exact_mod_cast hd) (by positivity)

include hd in
/-- Absorb the lower order terms of the homogeneous auxiliary bound in a common scale. -/
lemma auxDegreeBound_le_of_main {b H K Q : ℝ} (hB : 1 ≤ B)
    (hQ : affineBoxPower n d B ≤ Q) (hmain : b * B ^ boxExponent n d / H ^ heightExponent n d ≤ K * Q) :
    auxDegreeBound n d B b H ≤ (K + 2) * auxDegreeScale n d * Q := by
  have hD : 0 < degreeRoot n d := zero_lt_one.trans_le (degreeRoot_one_le hd)
  have hQ1 : 1 ≤ Q := (Real.one_le_rpow hB (by positivity)).trans hQ
  have hlog : Real.log B ≤ degreeRoot n d * Q := calc
    _ ≤ affineBoxPower n d B / (1 / degreeRoot n d) := Real.log_le_rpow_div (by linarith) (by positivity)
    _ ≤ _ := by simpa only [one_div, div_inv_eq_mul, mul_comm] using mul_le_mul_of_nonneg_left hQ hD.le
  have he : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B ≤ auxDegreeScale n d * Q := calc
    _ ≤ (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * (degreeRoot n d * Q) := by gcongr
    _ = d * Q := by rw [← mul_assoc, degreeRoot, ← Real.rpow_add (by exact_mod_cast hd), sub_add_cancel, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_rpow_four_sub_inv hd) (by linarith)
  have hp := le_mul_of_one_le_right (show 0 ≤ auxDegreeScale n d by positivity) hQ1
  unfold auxDegreeBound auxMainTerm
  linear_combination (auxDegreeScale n d) * hmain + he + hp

include hd in
/-- At the projective radius `p`, the power contributed by `p^d` in the leading
height cancels exactly the difference of the projective and affine exponents. -/
lemma scaling_identity (hp : 0 < p) :
    p ^ boxExponent n d = (p ^ d) ^ heightExponent n d * affineBoxPower n d p := by
  have hr : 0 < degreeRoot n d := zero_lt_one.trans_le (degreeRoot_one_le hd)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [← Real.rpow_natCast p d, ← Real.rpow_mul hp.le, affineBoxPower, ← Real.rpow_add hp]
  congr 1
  dsimp only [boxExponent, heightExponent]
  field_simp
  ring

section

variable (n : ℕ)

def scalingCost : ℝ := 6 * Real.exp (n + 1 : ℝ)
abbrev scaleBadCost := (4*(n+2 : ℝ)+5)*badHeightCost (n+2)
def scalingHeightCost : ℝ := 1 + 7*((n+1 : ℝ)*scaleBadCost n)
lemma scalingHeightCost_one_le : 1 ≤ scalingHeightCost n := by
  have := badHeightCost_nonneg (n+2)
  unfold scalingHeightCost scaleBadCost; apply le_add_of_nonneg_right
  positivity

end

include hd in
/-- A radius of order `d B` only changes the affine box power by a dimension constant. -/
theorem affine_power_scaling (hp : 1 ≤ p) (hB : 1 ≤ B)
    (hsize : p ≤ 6 * B * d) : affineBoxPower n d p ≤ scalingCost n * affineBoxPower n d B := by
  let e := 1 / degreeRoot n d
  have he : 0 ≤ e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := (div_le_one (by dsimp [degreeRoot]; positivity)).mpr (degreeRoot_one_le hd)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdp : (d : ℝ)^e ≤ Real.exp (n + 1 : ℝ) := by
    rw [Real.rpow_def_of_pos hd0]
    apply Real.exp_le_exp.mpr
    dsimp only [e]
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    simpa only [one_div, div_inv_eq_mul, mul_comm, degreeRoot] using Real.log_le_rpow_div hd0.le (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ))
  have h6 : (6 : ℝ)^e ≤ 6 := Real.rpow_le_self_of_one_le (by norm_num) he1
  calc
    _ ≤ (6 * B * d)^e := Real.rpow_le_rpow (by linarith) hsize he
    _ = (6 : ℝ)^e * B^e * (d : ℝ)^e := by rw [Real.mul_rpow (by positivity) hd0.le, Real.mul_rpow (by norm_num) (by linarith)]
    _ ≤ 6 * B^e * Real.exp (n + 1 : ℝ) := by gcongr
    _ = _ := by unfold scalingCost affineBoxPower; ring

section

variable (n : ℕ)

/-- The logarithmic and bad-reduction estimates are alternatives for the same model. -/
def affineAuxiliaryCharge (d : ℕ) (B L b : ℝ) :=
  min (b / L ^ heightExponent n d) (1 + Real.log B / d)

def affineHypersurfaceAuxiliaryConstant : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n * (scalingHeightCost n + 2) * scalingCost n

lemma affineHypersurfaceAuxiliaryConstant_pos : 0 < affineHypersurfaceAuxiliaryConstant n := by
  have := hypersurfaceAbsoluteAuxiliaryConstant_pos n
  have : 0 < scalingHeightCost n := zero_lt_one.trans_le (scalingHeightCost_one_le n)
  unfold affineHypersurfaceAuxiliaryConstant scalingCost
  positivity

end

include hd in
lemma log_scaling {p : ℝ} (hB : 1 ≤ B) (hp : 1 ≤ p)
    (hsize : p ≤ 6*B*d) : Real.log p ≤ Real.log B + 6*d := calc
  _ ≤ Real.log (B * (6 * d)) := Real.log_le_log (by linarith) (by linarith only [hsize])
  _ ≤ _ := by rw [Real.log_mul (by linarith) (by positivity)]; linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6 * d)]

/-- Combine the coefficient and logarithmic alternatives at the same scale. -/
theorem scaled_auxiliary_estimate {p b L H : ℝ} (hd : 0 < d) (hB : 1 ≤ B) (hp : 1 ≤ p)
    (hsize : p ≤ 6 * B * d) (hL : 1 ≤ L) (hb : 0 ≤ b) (hheight : p^d * L ≤ H)
    (hbad : b ≤ scaleBadCost n * (1 + Real.log H / (d:ℝ)^2)) :
    hypersurfaceAuxiliaryDegreeBound n d p b H ≤
      affineHypersurfaceAuxiliaryConstant n * auxDegreeScale n d * affineBoxPower n d B *
        (affineAuxiliaryCharge n d B L b + 1) := by
  let q := heightExponent n d
  let Y := p ^ d
  let K := scalingHeightCost n
  let T := affineAuxiliaryCharge n d B L b
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hY : 1 ≤ Y := one_le_pow₀ hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hYq : 0 < Y^q := by positivity
  have hc : 0 ≤ scaleBadCost n := mul_nonneg (by positivity) (badHeightCost_nonneg _)
  have hT : 0 ≤ T := le_min (by positivity) (by have := Real.log_nonneg hB; positivity)
  have hk1 : 1 ≤ K := scalingHeightCost_one_le n
  have hK : 0 ≤ K := zero_le_one.trans hk1
  have hlog := log_scaling hd hB hp hsize
  have hlog' : 1 + Real.log Y / (d : ℝ)^2 ≤ 7 * (1 + Real.log B / d) := by
    dsimp [Y]
    rw [Real.log_pow]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hlog hd0.le, mul_nonneg (Real.log_nonneg hB) hd0.le]
  have hratio : b / H^q ≤ K / Y^q * T := by
    dsimp only [T, affineAuxiliaryCharge]
    rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min ?_ ?_
    · calc
        _ ≤ b / (Y * L)^q := div_le_div₀ hb le_rfl (by positivity) (Real.rpow_le_rpow (by positivity) hheight hq)
        _ = 1 / Y^q * (b / L^q) := by rw [Real.mul_rpow (by linarith) (by linarith)]; ring
        _ ≤ _ := by gcongr
    · have hYH : Y ≤ H := (le_mul_of_one_le_right (by linarith) hL).trans hheight
      let R := (n+1 : ℝ)*scaleBadCost n
      calc
        _ ≤ R * (1 + Real.log Y / (d : ℝ)^2) / Y^q := by
          simpa only [Nat.cast_add, Nat.cast_one] using normalized_bad_factor (r := n+1) (by omega) hd hc hY hYH hbad
        _ ≤ R * (7 * (1 + Real.log B / d)) / Y^q := by gcongr
        _ = (7 * R) / Y^q * (1 + Real.log B / d) := by ring
        _ ≤ _ := by have := Real.log_nonneg hB; gcongr; exact le_add_of_nonneg_left zero_le_one
  have hmain : b * p ^ boxExponent n d / H^q ≤ K * T * affineBoxPower n d p := calc
    _ = (b / H^q) * (Y^q * affineBoxPower n d p) := by rw [scaling_identity hd (by linarith)]; ring
    _ ≤ (K / Y^q * T) * (Y^q * affineBoxPower n d p) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by field_simp
  have hcomp := auxDegreeBound_le_of_main hd hp le_rfl hmain
  have hc := (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  have hk : K * T + 2 ≤ (K + 2) * (T + 1) := by nlinarith
  calc
    _ ≤ hypersurfaceAbsoluteAuxiliaryConstant n * ((K * T + 2) * auxDegreeScale n d * affineBoxPower n d p) := mul_le_mul_of_nonneg_left hcomp hc
    _ ≤ hypersurfaceAbsoluteAuxiliaryConstant n * (((K + 2) * (T + 1)) * auxDegreeScale n d * (scalingCost n * affineBoxPower n d B)) := by
      gcongr
      exact affine_power_scaling hd hp hB hsize
    _ = _ := by unfold affineHypersurfaceAuxiliaryConstant; dsimp only [K, T]; ring

end
end CCDN
