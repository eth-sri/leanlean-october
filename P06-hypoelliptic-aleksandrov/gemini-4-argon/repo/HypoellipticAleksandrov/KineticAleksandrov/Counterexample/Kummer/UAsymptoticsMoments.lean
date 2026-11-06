module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsTaylor
import Mathlib.Tactic

/-!
# Gamma moments of the positive-axis expansion

This module evaluates the integral Taylor polynomial with the exact rising-factorial
coefficients of the source expansion.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/- Finite positive-axis U expansion in inverse powers of the argument. -/
def uExpansion (a b : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  z ^ (-a) * ∑ n ∈ Finset.range N,
    (-1 : ℝ) ^ n * poch a n * poch (a - b + 1) n /
      (n.factorial : ℝ) * z⁻¹ ^ n

/- Binomial coefficients written with the signed rising factorial. -/
theorem choose_eq_signed_poch (q : ℝ) (n : ℕ) :
    Ring.choose q n = (-1 : ℝ) ^ n * poch (-q) n / (n.factorial : ℝ) := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,
    ← descPochhammer_eval_eq_ascPochhammer, poch,
    ascPochhammer_eval_neg_eq_descPochhammer, smul_eq_mul]
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow]
  rw [← mul_assoc, hs]
  ring

/- Gamma recurrence at every nonnegative integer shift of a positive shape. -/
theorem Gamma_add_nat_eq_poch (a : Pos) (n : ℕ) :
    Real.Gamma (a.1 + n) = Real.Gamma a.1 * poch a.1 n := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero, poch_zero, mul_one]
  | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc,
        Real.Gamma_add_one (ne_of_gt (add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg n))),
        ih, poch_succ]
      ring

/- Evaluation of a scaled real Gamma kernel. -/
theorem integral_gammaKernel (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a - 1)) =
      z ^ (-a) * Real.Gamma a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hz
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow] at h
  simpa only [mul_comm] using h

/- The nth Gamma moment has precisely the source rising-factorial coefficient. -/
theorem integrableOn_gammaKernel_moment (a : Pos) (z : ℝ) (hz : 0 < z) (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n)
      (Ioi 0) volume := by
  apply IntegrableOn.congr_fun
    (integrableOn_gammaKernel (a.1 + n) z
      (add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg n)) hz) _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show a.1 + (n : ℝ) - 1 = (a.1 - 1) + (n : ℝ) by ring,
    Real.rpow_add ht, Real.rpow_natCast]
  ring

/- Integrability of the complete finite Taylor polynomial against the Gamma kernel. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
