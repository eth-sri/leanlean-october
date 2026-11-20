/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.CongruenceAuxiliary
import Mathlib.Algebra.Order.Star.Real
import CCDN.ForMathlib.Log
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile

/-! Numerical degree selection for the smooth-congruence auxiliary on a
surface. All constants are independent of coefficients and box radius. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A constant, depending on the degree `d` and the logarithmic height constant `K`, bounding
the height charge of the smooth-congruence determinant estimate for a surface of degree `d`
whose coefficient height `H` satisfies `log H ≤ K (log B + 1)`. -/
def surfaceCongruenceChargeConstant (d : ℕ) (K : ℝ) : ℝ :=
  Real.log (2 + 27 * (d : ℝ) ^ 4 * hypersurfaceHeightConstant 4 *
    (1 + K / (d : ℝ) ^ 2)) + 2 * mertensError + 1

/-- The constant `8 log d + 2 surfaceCongruenceChargeConstant d K + E + 6d + 22`, with `E` the
determinant error in dimension one, controlling the numerical gap between the upper and lower
bounds for surface congruence determinants. -/
def surfaceCongruenceGapConstant (d : ℕ) (K : ℝ) : ℝ :=
  8 * Real.log d + 2 * surfaceCongruenceChargeConstant d K +
    hypersurfaceDeterminantError 1 + 6 * d + 22

private theorem surface_congruence_charge_le {d : ℕ}
    {K B H Q : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H) (hQ : 0 ≤ Q)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    congruenceHeightCharge 4 d H Q ≤
      Real.log (1 + Real.log B + Q) + surfaceCongruenceChargeConstant d K := by
  have hc := hypersurfaceHeightConstant_one_le 4
  have hlogH := Real.log_nonneg hH
  let A := 27 * (d : ℝ) ^ 4 * hypersurfaceHeightConstant 4
  let T := 1 + Real.log B + Q
  have hT : 1 ≤ T := by dsimp [T]; linarith [Real.log_nonneg hB]
  have hdiv : Real.log H / (d : ℝ) ^ 2 ≤ K / (d : ℝ) ^ 2 * T := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [T]
    nlinarith
  have hA : 0 ≤ A := by positivity
  have hinside : 1 + A * (1 + Real.log H / (d : ℝ) ^ 2) + Q ≤
      (2 + A * (1 + K / (d : ℝ) ^ 2)) * T := by
    have : 1 + Q ≤ T := by dsimp [T]; linarith [Real.log_nonneg hB]
    have := mul_le_mul_of_nonneg_left (add_le_add hT hdiv) hA
    linarith
  have hh := Real.log_le_log (by positivity) hinside
  rw [Real.log_mul (by positivity) (by positivity)] at hh
  simp only [congruenceHeightCharge, surfaceCongruenceChargeConstant, ← mul_assoc]
  dsimp only [T, A] at hh
  linarith

private theorem surface_congruence_lower_eq (d s : ℕ) (H Q : ℝ) :
    affineCongruenceDeterminantLower 1 d s H Q =
      (Real.sqrt 2 / 3 * (s : ℝ) * Real.sqrt s) *
        (Real.log s + 2 * Q - 8 * Real.log d -
          2 * congruenceHeightCharge 4 d H Q - hypersurfaceDeterminantError 1) -
            3 * s * Q := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hp : (s : ℝ) ^ (1 + 1 / 2 : ℝ) = s * Real.sqrt s := by
    rw [Real.rpow_add' hs (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  norm_num at hp
  unfold affineCongruenceDeterminantLower hypersurfaceRankLowerBound hypersurfaceDeterminantMain factorialRoot
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, Nat.cast_mul,
    Nat.cast_one, Nat.cast_add, Nat.cast_succ, mul_one]
  rw [hp, ← Real.sqrt_eq_rpow]
  ring

private theorem surface_congruence_gap_of_log_rank {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) {K B H Q : ℝ}
    (hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H) (hQ : 0 ≤ Q)
    (hheight : Real.log H ≤ K * (Real.log B + 1))
    (hroot : 1 + Real.log B + Q ≤ Real.sqrt (s : ℝ))
    (hrank : (2 / Real.sqrt (d : ℝ)) * Real.log B +
        2 * Real.log (1 + Real.log B + Q) + surfaceCongruenceGapConstant d K ≤
      Real.log s + 2 * Q) :
    Real.log (s.factorial : ℝ) +
      ((2 / 3 : ℝ) * s * Real.sqrt (2 * s / (d : ℝ)) + (2 * d + 2) * s) *
        Real.log B < affineCongruenceDeterminantLower 1 d s H Q := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlogB := Real.log_nonneg hB
  have hfac : Real.log (s.factorial : ℝ) ≤ s * (Real.sqrt s * 2) := by
    simpa [Real.sqrt_eq_rpow, div_eq_mul_inv] using
      Real.log_factorial_le_mul_rpow s (show (0 : ℝ) < 1 / 2 by norm_num)
  have hcharge := surface_congruence_charge_le (d := d) hK hB hH hQ hheight
  let A : ℝ := Real.sqrt 2 / 3 * s * Real.sqrt s
  have hA : 0 < A := by positivity
  have herr : Real.log (s.factorial : ℝ) + (2 * d + 2) * s * Real.log B + 3 * s * Q ≤
      A * (6 * d + 21) := by
    have hl : Real.log B ≤ Real.sqrt (s : ℝ) := by linarith
    have hq : Q ≤ Real.sqrt (s : ℝ) := by linarith
    have h₂ : (1 : ℝ) ≤ Real.sqrt 2 := by simp
    dsimp only [A]
    linarith only [hfac, mul_le_mul_of_nonneg_left hl (show 0 ≤ (2 * (d : ℝ) + 2) * s by positivity),
      mul_le_mul_of_nonneg_left hq (show 0 ≤ 3 * (s : ℝ) by positivity),
      mul_le_mul_of_nonneg_right h₂ (show 0 ≤ (s : ℝ) * Real.sqrt s * (2 * d + 7) by positivity)]
  rw [surface_congruence_lower_eq, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]
  unfold surfaceCongruenceGapConstant at hrank
  have h := mul_le_mul_of_nonneg_left (show
      (2 / Real.sqrt (d : ℝ)) * Real.log B + (6 * d + 22) ≤
        Real.log s + 2 * Q - 8 * Real.log d - 2 * congruenceHeightCharge 4 d H Q -
          hypersurfaceDeterminantError 1 by linarith) hA.le
  dsimp only [A] at h hA herr
  grind

/-- The constant `d + 2 (exp (G / 2) + 1) + 1`, with `G` the gap constant
`surfaceCongruenceGapConstant d K`, which scales the degree of the surface congruence
auxiliaries. -/
def surfaceCongruenceDegreeConstant (d : ℕ) (K : ℝ) : ℝ :=
  d + 2 * (Real.exp (surfaceCongruenceGapConstant d K / 2) + 1) + 1

/-- The auxiliary degree constant `surfaceCongruenceDegreeConstant d K` is positive. -/
theorem surfaceCongruenceDegreeConstant_pos (d : ℕ) (K : ℝ) :
    0 < surfaceCongruenceDegreeConstant d K := by
  unfold surfaceCongruenceDegreeConstant
  positivity

/-- One integer degree, with a constant fixed before the height and congruences,
works for every standard-monomial rank satisfying the elementary power bound. -/
private theorem surface_congruence_degree_selection {d : ℕ} (hd : 0 < d)
    {K B H Q : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H) (hQ : 0 ≤ Q)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    ∃ M : ℕ, d ≤ M ∧
      (M : ℝ) ≤ surfaceCongruenceDegreeConstant d K *
        (B ^ (1 / Real.sqrt (d : ℝ)) / Real.exp Q + 1) * (1 + Real.log B + Q) ∧
      ∀ s : ℕ, (d : ℝ) * ((M : ℝ) - d + 1) ^ 2 / 2 ≤ s →
        surfaceWeightedDeterminantUpper d s B <
          affineCongruenceDeterminantLower 1 d s H Q := by
  let T := 1 + Real.log B + Q
  let ρ := B ^ (1 / Real.sqrt (d : ℝ)) / Real.exp Q
  let E := Real.exp (surfaceCongruenceGapConstant d K / 2)
  let S := (E + 1) * (ρ + 1) * T
  have hB0 : 0 < B := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT : 1 ≤ T := by linarith [Real.log_nonneg hB]
  have hT0 : 0 < T := by linarith
  have hρ : 0 < ρ := by positivity
  have hE : 0 < E := Real.exp_pos _
  have hS : 0 < S := by positivity
  have hW : 1 ≤ (ρ + 1) * T := by nlinarith
  let M := d + ⌈2 * S⌉₊
  refine ⟨M, Nat.le_add_right _ _, ?_, fun s hs => ?_⟩
  · have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 * S by positivity)
    have hmul := mul_le_mul_of_nonneg_left hW (show 0 ≤ (d : ℝ) + 1 by positivity)
    change (M : ℝ) ≤ ((d : ℝ) + 2 * (E + 1) + 1) * (ρ + 1) * T
    simp only [M, Nat.cast_add]
    nlinarith [show S = (E + 1) * (ρ + 1) * T from rfl]
  have hlow : 2 * S ≤ (M : ℝ) - d + 1 := by
    simpa only [M, Nat.cast_add] using (Nat.le_ceil (2 * S)).trans (by linarith)
  have hsq : S ^ 2 ≤ (s : ℝ) := by
    have := pow_le_pow_left₀ (by positivity) hlow 2
    nlinarith only [this, hs, mul_le_mul_of_nonneg_right hdR (sq_nonneg ((M : ℝ) - d + 1))]
  have hsN : 0 < s := Nat.cast_pos.mp ((sq_pos_of_pos hS).trans_le hsq)
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  have hroot : T ≤ Real.sqrt (s : ℝ) := (le_mul_of_one_le_left hT0.le (by nlinarith [mul_nonneg hE.le hρ.le])).trans hsqrt
  have hle : E * ρ * T ≤ S := by dsimp only [S]; gcongr <;> linarith
  have hlog := Real.log_le_log (by positivity) (hle.trans hsqrt)
  rw [Real.log_sqrt (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul hE.ne' hρ.ne'] at hlog
  dsimp only [E, ρ, T] at hlog
  rw [Real.log_exp, Real.log_div (by positivity) (by positivity),
    Real.log_rpow hB0, Real.log_exp] at hlog
  exact surface_congruence_gap_of_log_rank hd hsN hK hB hH hQ hheight hroot (by linear_combination 2 * hlog)

/-- The smooth residue classes have a proper auxiliary of degree
O_d,K((B^(1/√d)/exp Q + 1)(1 + log B + Q)). -/
theorem exists_surface_congruence_auxiliary
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} (hK : 0 ≤ K) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : Real.log H ≤ K * (Real.log B + 1))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → IntPoint 3)
    (ha : ∀ p ∈ P, MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun j => (a p j : ZMod p)) f = 0)
    (hsmooth : ∀ p ∈ P, ∃ j, MvPolynomial.eval (fun i => (a p i : ZMod p))
      (MvPolynomial.pderiv j (MvPolynomial.map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧
      ¬ MvPolynomial.map (Int.castRingHom ℚ) f ∣ MvPolynomial.map (Int.castRingHom ℚ) g ∧
      (g.totalDegree : ℝ) ≤ surfaceCongruenceDegreeConstant f.totalDegree K *
        (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
          Real.exp (∑ p ∈ P, Real.log p) + 1) *
        (1 + Real.log B + ∑ p ∈ P, Real.log p) ∧
      ∀ x ∈ affineCongruencePoints f B P a, MvPolynomial.eval x g = 0 := by
  have hQ : 0 ≤ ∑ p ∈ P, Real.log p := Finset.sum_nonneg fun p hp =>
    Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)
  obtain ⟨M, hdM, hM, hgap⟩ :=
    surface_congruence_degree_selection hd hK hB hH hQ hheight
  have hg := hgap _ (hypersurface_rank_power_bounds (r := 2) hdM).1
  obtain ⟨g, hg0, hgproper, hgM, hgz⟩ := exists_surface_congruence_auxiliary_of_gap
    f hir hd H hH hcoeff hdM hB P hP a ha hsmooth hg
  refine ⟨g, hg0, hgproper, le_trans ?_ hM, hgz⟩
  exact_mod_cast hgM

end
end CCDN
