/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.ScaledPlaneCount
import CCDN.ForMathlib.Log

/-! The scaling-prime interval yields the affine box exponent 1/d. These
numerical bounds are independent of the coefficient height. -/

@[expose] public section
namespace CCDN
open Real

/-- A coefficient-uniform affine count with exponent 1/d, conditional on the
sharp finite-field estimate and a prime p in [B/A,B] not dividing f(0). -/
theorem scaled_plane_finite_count_one_over_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (hd : 0 < f.totalDegree) {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    {A B C : ℝ} (hzB : IsBoxZeroFamily f B z) (hA : 1 ≤ A) (hpB : (p : ℝ) ≤ B) (hBp : B ≤ A * p)
    (hC : 0 ≤ C)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤
      (38 + 8 * Real.exp (heightDeterminantError C + 20) +
        2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * A) *
      (f.totalDegree : ℝ) ^ 3 * B ^ (1 / (f.totalDegree : ℝ)) *
        (Real.log B + f.totalDegree) := by
  have hB := hzB.one_le_radius
  let d := f.totalDegree
  let Q := B ^ (1 / (d : ℝ))
  let U := Real.log B + d
  let E := 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14
  let K₁ := 4 + E * Real.exp 2 * A
  let K₂ := 34 + 8 * Real.exp (heightDeterminantError C + 20)
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hB0 : 0 < B := by linarith
  have hp1 : (1 : ℝ) ≤ p := mod_cast hp.one_lt.le
  have hp0R : (0 : ℝ) < p := by linarith
  have hlogB := Real.log_nonneg hB
  have hlogp := Real.log_nonneg hp1
  have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hU : (d : ℝ) ≤ U := by dsimp [U]; linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  have hrest : (0 : ℝ) ≤ (d : ℝ) ^ 3 * Q * U := by dsimp [U]; positivity
  have hdeg : ((d : ℝ) + 1) ^ (2 / (d : ℝ)) ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    rw [← mul_div_assoc, div_le_iff₀ hd0]
    linarith [Real.log_add_one_le_self hd0.le]
  have hexp : (1 : ℝ) / d ≤ 1 := (div_le_iff₀ hd0).mpr (by linarith)
  have hquot : (B / p) ^ (1 / (d : ℝ)) ≤ A :=
    (Real.rpow_le_rpow (div_nonneg hB0.le hp0R.le) ((div_le_iff₀ hp0R).mpr hBp)
      (by positivity)).trans
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA hexp)
  have hratio : (((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / (p : ℝ) ^ (1 / (d : ℝ)) ≤
      Real.exp 2 * A * Q := by
    have he : (((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / (p : ℝ) ^ (1 / (d : ℝ)) =
        ((d : ℝ) + 1) ^ (2 / (d : ℝ)) * (B / p) ^ (1 / (d : ℝ)) * Q := by
      dsimp only [Q]
      rw [Real.mul_rpow (by linarith) hB0.le, Real.div_rpow hB0.le hp0R.le,
        show (2 : ℝ) / d = 1 / d + 1 / d by ring, Real.rpow_add hB0]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hdeg hquot (by positivity) (Real.exp_pos _).le) (by dsimp [Q]; positivity)
  have hnumB : 1 + Real.log p / d ≤ 1 + Real.log B / d := by gcongr
  have hterm : E * (d : ℝ) ^ 3 * (1 + Real.log p / d) *
        ((((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / (p : ℝ) ^ (1 / (d : ℝ))) ≤
      E * Real.exp 2 * A * (d : ℝ) ^ 2 * Q * U := by
    have hh := mul_le_mul hnumB hratio
      (div_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hp0R.le _)) (by positivity)
    convert mul_le_mul_of_nonneg_left hh (mul_nonneg hE (pow_nonneg hd0.le 3)) using 1
    · ring
    · dsimp only [Q, U]; field_simp; ring
  have hlogR : Real.log (((d : ℝ) + 1) * B) ≤ d + Real.log B := by
    rw [Real.log_mul (by positivity) hB0.ne']
    linarith [Real.log_add_one_le_self hd0.le]
  have hrest_sm : (d : ℝ) + Real.log (((d : ℝ) + 1) * B) + 2 ≤ 4 * (d : ℝ) ^ 2 * Q * U := by
    have hprod : 1 ≤ (d : ℝ) ^ 2 * Q := one_le_mul_of_one_le_of_one_le (by nlinarith) hQ
    dsimp only [U]
    nlinarith [mul_le_mul_of_nonneg_right hprod (show 0 ≤ Real.log B + d by positivity)]
  have hb_sm : scaledPlaneAuxiliaryDegreeBound d C (((d : ℝ) + 1) * B) p ≤
      K₁ * (d : ℝ) ^ 2 * Q * U := by
    unfold scaledPlaneAuxiliaryDegreeBound
    calc _ = ((d : ℝ) + Real.log (((d : ℝ) + 1) * B) + 2) + E * (d : ℝ) ^ 3 *
          (1 + Real.log p / d) *
          ((((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / (p : ℝ) ^ (1 / (d : ℝ))) := by dsimp [E]; ring
      _ ≤ 4 * (d : ℝ) ^ 2 * Q * U + E * Real.exp 2 * A * (d : ℝ) ^ 2 * Q * U :=
        add_le_add hrest_sm hterm
      _ = _ := by dsimp [K₁]; ring
  have hsmall : (d : ℝ) * scaledPlaneAuxiliaryDegreeBound d C (((d : ℝ) + 1) * B) p ≤
      K₁ * ((d : ℝ) ^ 3 * Q * U) :=
    (mul_le_mul_of_nonneg_left hb_sm hd0.le).trans_eq (by ring)
  have hlarge : K₂ * (d : ℝ) ^ 4 ≤ K₂ * ((d : ℝ) ^ 3 * Q * U) := by
    apply mul_le_mul_of_nonneg_left _ hK₂
    have ht := mul_le_mul_of_nonneg_left (show (d : ℝ) ≤ Q * U by nlinarith) (pow_nonneg hd0.le 3)
    nlinarith only [ht]
  have hb : (t : ℝ) ≤ (K₁ + K₂) * ((d : ℝ) ^ 3 * Q * U) :=
    (scaled_plane_finite_count f hprim hir hd hp hp0 z hinj hzB hpB hC hcount).trans
      (max_le (hsmall.trans (mul_le_mul_of_nonneg_right (by linarith) hrest))
        (hlarge.trans (mul_le_mul_of_nonneg_right (by linarith) hrest)))
  convert hb using 1
  simp only [K₁, K₂, E, Q, U, d]; ring

end CCDN
