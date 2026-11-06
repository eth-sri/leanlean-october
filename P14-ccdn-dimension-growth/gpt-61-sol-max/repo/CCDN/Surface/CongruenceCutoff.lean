/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Surface.CongruenceAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
import Mathlib.Algebra.Order.Star.Real

/-! Numerical degree selection for the smooth-congruence auxiliary on a
surface. All constants are independent of coefficients and box radius. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A constant, depending on the degree `d` and the logarithmic height constant `K`, bounding
the height charge of the smooth-congruence determinant estimate for a surface of degree `d`
whose coefficient height `H` satisfies `log H ≤ K (log B + 1)`. -/
def surfaceCongruenceChargeConstant (d : ℕ) (K : ℝ)  :=
  Real.log (2 + 27 * ↑d ^ 4 * hypersurfaceHeightConstant 4 *
    (1 + K / ↑d ^ 2)) + 2 * mertensError + 1

/-- The constant `8 log d + 2 surfaceCongruenceChargeConstant d K + E + 6d + 22`, with `E` the
determinant error in dimension one, controlling the numerical gap between the upper and lower
bounds for surface congruence determinants. -/
def surfaceCongruenceGapConstant (d : ℕ) (K : ℝ)  :=
  8 * Real.log d + 2 * surfaceCongruenceChargeConstant d K +
    hypersurfaceDeterminantError 1 + 6 * d + 22

variable {d : ℕ} (hd : 0 < d) {K B H Q : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H) (hQ : 0 ≤ Q) (hheight : Real.log H ≤ K * (Real.log B + 1))

include hd hK hB hH hQ hheight in
private theorem surface_congruence_charge_le  :
    congruenceHeightCharge 4 d H Q ≤
      Real.log (1 + Real.log B + Q) + surfaceCongruenceChargeConstant d K := by
  have hc :=
    zero_le_one.trans (hypersurfaceHeightConstant_one_le 4)
  have hlogB := Real.log_nonneg hB
  have hlogH := Real.log_nonneg hH
  have hheight' : Real.log H ≤ K * (1 + Real.log B + Q) := by nlinarith
  let A := 27 * ↑d ^ 4 * hypersurfaceHeightConstant 4
  have hA : 0 ≤ A := by positivity
  have hdiv := div_le_div_of_nonneg_right hheight' (sq_nonneg ↑d)
  have hinside : 1 + A * (1 + Real.log H / ↑d ^ 2) + Q ≤
      (2 + A * (1 + K / ↑d ^ 2)) * (1 + Real.log B + Q) := by
    have hm := mul_le_mul_of_nonneg_left hdiv hA
    have he : K * (1 + Real.log B + Q) / ↑d ^ 2 =
        K / ↑d ^ 2 * (1 + Real.log B + Q) := by ring
    rw [he] at hm
    nlinarith
  have hleft : 0 < 1 + A * (1 + Real.log H / ↑d ^ 2) + Q := by positivity
  have hright : 0 < 2 + A * (1 + K / ↑d ^ 2) := by positivity
  have hh := Real.log_le_log hleft hinside
  rw [Real.log_mul hright.ne' (by linarith : (1 + Real.log B + Q) ≠ 0)] at hh
  unfold congruenceHeightCharge surfaceCongruenceChargeConstant
  dsimp only [A] at hh
  simp only [mul_assoc] at hh ⊢
  nlinarith

private theorem surface_congruence_lower_eq (d s : ℕ) (H Q : ℝ) :
    affineCongruenceDeterminantLower 1 d s H Q =
      (Real.sqrt 2 / 3 * ↑s * Real.sqrt s) *
        (Real.log s + 2 * Q - 8 * Real.log d -
          2 * congruenceHeightCharge 4 d H Q - hypersurfaceDeterminantError 1) -
            3 * s * Q := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hp : ↑s ^ (1 + 1 / 2 : ℝ) = s * Real.sqrt s := by
    rw [Real.rpow_add' hs (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  norm_num at hp
  unfold affineCongruenceDeterminantLower hypersurfaceDeterminantMain
  norm_num only [factorialRoot, Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, Nat.cast_mul,
    Nat.cast_one, Nat.cast_add, Nat.cast_succ, mul_one]
  rw [hp, ← Real.sqrt_eq_rpow]
  ring

private theorem surface_congruence_gap_of_log_rank {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) {K B H Q : ℝ}
    (hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H) (hQ : 0 ≤ Q)
    (hheight : Real.log H ≤ K * (Real.log B + 1))
    (hroot : 1 + Real.log B + Q ≤ Real.sqrt ↑s)
    (hrank : (2 / Real.sqrt ↑d) * Real.log B +
        2 * Real.log (1 + Real.log B + Q) + surfaceCongruenceGapConstant d K ≤
      Real.log s + 2 * Q) :
    Real.log ↑s.factorial +
      ((2 / 3 : ℝ) * s * Real.sqrt (2 * s / ↑d) + (2 * d + 2) * s) *
        Real.log B < affineCongruenceDeterminantLower 1 d s H Q := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogB := Real.log_nonneg hB
  have hfac := by
    have hh : ↑s.factorial ≤ (s : ℝ) ^ s := by exact_mod_cast Nat.factorial_le_pow s
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hh
  have hlog := by
    have hh := log_le_dimension_root (r := 2) (by omega) hsR
    simpa only [Nat.cast_ofNat, ← Real.sqrt_eq_rpow] using hh
  have hcharge := surface_congruence_charge_le hd hK hB hH hQ hheight
  have hsqrt2 : 1 ≤ Real.sqrt 2 := by
    simp_all
  let A : ℝ := Real.sqrt 2 / 3 * s * Real.sqrt s
  have hA : 0 < A := by positivity
  have hsplit : Real.sqrt (2 * s / ↑d) =
      Real.sqrt 2 * Real.sqrt s / Real.sqrt d := by
    simp_all
  have hmain : (2 / 3 : ℝ) * s * Real.sqrt (2 * s / ↑d) =
      A * (2 / Real.sqrt ↑d) := by
    grind
  have herr : Real.log ↑s.factorial + (2 * d + 2) * s * Real.log B + 3 * s * Q ≤
      A * (6 * d + 21) := by
    have hb : Real.log B ≤ Real.sqrt ↑s := by linarith
    have hb' := mul_le_mul_of_nonneg_left hb
      (show 0 ≤ (2 * (d : ℝ) + 2) * s by positivity)
    have hA' : ↑s * Real.sqrt s ≤ 3 * A := by
      have hh := mul_le_mul_of_nonneg_right hsqrt2
        (show 0 ≤ ↑s * Real.sqrt s by positivity)
      dsimp only [A]
      nlinarith
    nlinarith
  have hbracket :
      (2 / Real.sqrt ↑d) * Real.log B + (6 * d + 22) ≤
        Real.log s + 2 * Q - 8 * Real.log d -
          2 * congruenceHeightCharge 4 d H Q - hypersurfaceDeterminantError 1 := by
    unfold surfaceCongruenceGapConstant at hrank
    linarith
  rw [surface_congruence_lower_eq]
  rw [hmain]
  change _ < A * _ - _
  nlinarith

/-- The constant `d + 2 (exp (G / 2) + 1) + 1`, with `G` the gap constant
`surfaceCongruenceGapConstant d K`, which scales the degree of the surface congruence
auxiliaries. -/
def surfaceCongruenceDegreeConstant (d : ℕ) (K : ℝ)  :=
  d + 2 * (Real.exp (surfaceCongruenceGapConstant d K / 2) + 1) + 1

/-- The auxiliary degree constant `surfaceCongruenceDegreeConstant d K` is positive. -/
theorem surfaceCongruenceDegreeConstant_pos (d : ℕ) (K : ℝ) :
    0 < surfaceCongruenceDegreeConstant d K := by
  unfold surfaceCongruenceDegreeConstant
  positivity

include hd hK hB hH hQ hheight in
/-- One integer degree, with a constant fixed before the height and congruences,
works for every standard-monomial rank satisfying the elementary power bound. -/
private theorem surface_congruence_degree_selection  :
    ∃ M : ℕ, d ≤ M ∧
      ↑M ≤ surfaceCongruenceDegreeConstant d K *
        (B ^ (1 / Real.sqrt ↑d) / Real.exp Q + 1) * (1 + Real.log B + Q) ∧
      ∀ s : ℕ, ↑d * ((M : ℝ) - d + 1) ^ 2 / 2 ≤ s →
        surfaceWeightedDeterminantUpper d s B <
          affineCongruenceDeterminantLower 1 d s H Q := by
  let T := 1 + Real.log B + Q
  let ρ := B ^ (1 / Real.sqrt ↑d) / Real.exp Q
  let E := Real.exp (surfaceCongruenceGapConstant d K / 2) + 1
  let S := E * (ρ + 1) * T
  have hB0 := zero_lt_one.trans_le hB
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT : 1 ≤ T := by dsimp only [T]; linarith [Real.log_nonneg hB]
  have hT0 := zero_lt_one.trans_le hT
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hE : 1 ≤ E := by
    dsimp only [E]; linarith [Real.exp_pos (surfaceCongruenceGapConstant d K / 2)]
  have hE0 := zero_lt_one.trans_le hE
  have hS0 : 0 < S := by dsimp only [S]; positivity
  have hST := by
    have hh := mul_le_mul hE (show 1 ≤ ρ + 1 by linarith) (by norm_num) hE0.le
    have hh' := mul_le_mul_of_nonneg_right hh hT0.le
    simpa only [one_mul] using hh'
  let M := d + ⌈2 * S⌉₊
  have hMd : d ≤ M := Nat.le_add_right _ _
  have hMl : 2 * S ≤ ↑M - d + 1 := by
    have hh := Nat.le_ceil (2 * S)
    dsimp only [M]
    push_cast
    linarith
  have hMu : ↑M ≤ surfaceCongruenceDegreeConstant d K * (ρ + 1) * T := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * S by positivity)
    have hprod : 1 ≤ (ρ + 1) * T := by
      nlinarith
    dsimp only [M] at *
    push_cast
    change _ ≤ (↑d + 2 * E + 1) * (ρ + 1) * T
    dsimp only [S] at hh
    nlinarith
  refine ⟨M, hMd, hMu, ?_⟩
  intro s hs
  have hsq : S ^ 2 ≤ ↑s := by
    nlinarith [sq_nonneg S]
  have hsR := lt_of_lt_of_le (sq_pos_of_pos hS0) hsq
  have hsN := by exact_mod_cast hsR
  have hroot :=
    hST.trans (Real.le_sqrt_of_sq_le hsq)
  have hlogS := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (sq_pos_of_pos hS0) hsq
  have hlogE : surfaceCongruenceGapConstant d K / 2 ≤ Real.log E := by
    grind [Real.log_le_log, Real.exp_pos, Real.log_exp]
  have hlogρ : Real.log ρ ≤ Real.log (ρ + 1) :=
    Real.log_le_log hρ (by linarith)
  have hρeq : Real.log ρ = (1 / Real.sqrt ↑d) * Real.log B - Q := by
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_rpow hB0, Real.log_exp]
  have hSeq : Real.log S = Real.log E + Real.log (ρ + 1) + Real.log T := by
    rw [Real.log_mul (by positivity) hT0.ne', Real.log_mul hE0.ne' (by positivity)]
  have hrank : (2 / Real.sqrt ↑d) * Real.log B +
      2 * Real.log T + surfaceCongruenceGapConstant d K ≤ Real.log s + 2 * Q := by
    grind
  exact surface_congruence_gap_of_log_rank hd hsN hK hB hH hQ hheight hroot hrank

/-- The smooth residue classes have a proper auxiliary of degree
O_d,K((B^(1/√d)/exp Q + 1)(1 + log B + Q)). -/
theorem exists_surface_congruence_auxiliary
    (f : CCDN.IntegerPolynomial 3)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} (hK : 0 ≤ K) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : Real.log H ≤ K * (Real.log B + 1))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → IntPoint 3)
    (ha : ∀ p ∈ P, MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun j => (a p j : ZMod p)) f = 0)
    (hsmooth : ∀ p ∈ P, ∃ j, MvPolynomial.eval (fun i => (a p i : ZMod p))
      (MvPolynomial.pderiv j (MvPolynomial.map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    ∃ g : CCDN.IntegerPolynomial 3,
      ¬ CCDN.rationalPolynomial f ∣ CCDN.rationalPolynomial g ∧
      ↑g.totalDegree ≤ surfaceCongruenceDegreeConstant f.totalDegree K *
        (B ^ (1 / Real.sqrt ↑f.totalDegree) /
          Real.exp (∑ p ∈ P, Real.log p) + 1) *
        (1 + Real.log B + ∑ p ∈ P, Real.log p) ∧
      ∀ x ∈ affineCongruencePoints f B P a, MvPolynomial.eval x g = 0 := by
  have hQ : 0 ≤ ∑ p ∈ P, Real.log p := Finset.sum_nonneg fun p hp =>
    Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)
  obtain ⟨M, hdM, hM, hgap⟩ :=
    surface_congruence_degree_selection hd hK hB hH hQ hheight
  have hf : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  have hg := hgap (surfaceCongruenceRank f M) (surface_congruence_rank_power_bounds f hf hdM).1
  obtain ⟨g, hgproper, hgM, hgz⟩ := exists_surface_congruence_auxiliary_of_gap
    f hir hd H hH hcoeff hdM hB P hP a ha hsmooth hg
  refine ⟨g, hgproper, le_trans ?_ hM, hgz⟩
  exact_mod_cast hgM

end
end CCDN
