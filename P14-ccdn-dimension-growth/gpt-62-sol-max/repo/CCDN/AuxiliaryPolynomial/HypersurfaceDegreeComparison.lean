/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfaceRankLogarithm
public import CCDN.AuxiliaryPolynomial.DegreeBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.HypersurfaceKernelRatio
public import CCDN.AuxiliaryPolynomial.HypersurfaceRankRoots
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import CCDN.ForMathlib.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The small- and large-height bounds start with the same reciprocal and
kernel estimates for the exact homogeneous Hilbert rank. -/

@[expose] public section
namespace CCDN
noncomputable section

private lemma log_degree_comparison {r d M : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hM : 2 * d ≤ M)
    {b l c E : ℝ} (hc : NormalizedRankComparison r d M b l c E) :
    ∃ a k : ℝ, (M : ℝ) - d ≤ a ∧ a ≤ M + r ∧ (M : ℝ) - d * (r + 1 : ℝ) ≤ k ∧
      a * ((d : ℝ) ^ (1 / (r : ℝ)) *
        (r * Real.log M - ((4 * (r : ℝ) - 1) * Real.log d + r * c + E +
          hypersurfaceRankLogError r))) ≤ (M : ℝ) * ((r + 1 : ℝ) * b) - k * (l / d) := by
  have hdM : d ≤ M := by omega
  let s := hypersurfaceRank (r + 1) d M
  have hs : 0 < s := hypersurface_rank_pos hdM hd
  let X := (d : ℝ) ^ (1 / (r : ℝ))
  let a := hypersurfaceRankRoot r s / X
  let K : ℝ := (r + 1 + (M - d)).choose (M - d)
  have hX : 0 < X := by positivity
  have hd0 : (0 : ℝ) < d := by positivity
  have hr1 : (0 : ℝ) < r + 1 := by positivity
  obtain ⟨ha, ha'⟩ := hypersurface_rank_root_bounds hrpos hdM
  refine ⟨a, (d : ℝ) * (r + 1 : ℝ) * K / s, (le_div_iff₀ hX).mpr (by linarith),
    (div_le_iff₀ hX).mpr (by linarith), hypersurface_kernel_ratio_lower hdM hd, ?_⟩
  change (hypersurfaceRankRoot r s / X) * (X * _) ≤ _
  rw [← mul_assoc, div_mul_cancel₀ _ hX.ne']
  have hlog := hypersurface_rank_log_lower (r := r) hd hM
  have hlog' := mul_le_mul_of_nonneg_left hlog (show 0 ≤ hypersurfaceRankRoot r s by positivity)
  change hypersurfaceRankRoot r s * _ ≤ _ at hc
  have hk : (d : ℝ) * (r + 1 : ℝ) * K / s * (l / d) = (r + 1 : ℝ) * (K / s * l) := by
    field_simp
  rw [hk]
  linarith

/-- Dimension-dependent error in the logarithmic degree bound at small height. -/
def hypersurfaceSmallHeightError (r : ℕ) (E T : ℝ) : ℝ :=
  (E + hypersurfaceRankLogError r + 8 * (r + 1 : ℝ) ^ 2 + T) / r

/-- Solve the normalized rank inequality at small height, including the loss from positioning. -/
theorem hypersurface_small_height_degree_bound {n d M : ℕ}
    (hd : 0 < d) (hM : 2 * d ≤ M)
    {B L H A E T : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hH : 0 < H) (hA : 0 < A)
    (hheight : Real.log L ≤ 2 * d * (n + 2 : ℝ) * Real.log B)
    (hscale : (d : ℝ) * Real.log B ≤ degreeRoot n d * M)
    (hposition : Real.log H ≤ Real.log L + T * d * degreeRoot n d)
    (hcomparison : NormalizedRankComparison (n + 1) d M (Real.log B) (Real.log L) (Real.log A) E) :
    (M : ℝ) ≤ Real.exp (hypersurfaceSmallHeightError (n + 1) E T) * auxMainTerm n d B A H := by
  let r := n + 1
  let R := (r : ℝ) + 1
  let X := (d : ℝ) ^ (1 / (r : ℝ))
  let b := R * Real.log B
  let l := Real.log L / d
  have hrpos : 0 < r := by omega
  have hr : (r : ℝ) = n + 1 := by simp [r]
  have hR : R = n + 2 := by simp [R, hr]; ring
  have hXd : X = degreeRoot n d := by simp [X, hr, degreeRoot]
  rw [← hXd] at hscale hposition
  have hd0 : (0 : ℝ) < d := by positivity
  have hr0 : (0 : ℝ) < r := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM' : (2 : ℝ) * d ≤ M := by exact_mod_cast hM
  have hX : 0 < X := by positivity
  have hb : 0 ≤ b := mul_nonneg (by positivity) (Real.log_nonneg hB)
  have hl : 0 ≤ l := div_nonneg (Real.log_nonneg hL) (by positivity)
  have hh : l ≤ 2 * b := (div_le_iff₀ hd0).mpr (by dsimp only [b]; rw [hR]; linarith)
  obtain ⟨a, k, ha, ha', hk, hc⟩ := log_degree_comparison (r := r) hrpos hd hM hcomparison
  have ha0 : 0 < a := by linarith
  have hq : (M : ℝ) * b - k * l ≤ a * (b - l) + d * b + (r + d * R) * l := by
    linarith only [mul_le_mul_of_nonneg_right ha hb, mul_le_mul_of_nonneg_right ha' hl,
      mul_le_mul_of_nonneg_right hk hl]
  have herr : (r + d * R) * l ≤ (4 * R - 1) * (d * b) := calc
    _ ≤ (d * r + d * R) * (2 * b) := by gcongr; simpa using mul_le_mul_of_nonneg_right hd1 hr0.le
    _ ≤ _ := by dsimp [R]; nlinarith only [mul_nonneg hd0.le hb]
  have hbb : (d : ℝ) * b ≤ R * X * M := by
    linarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ R by positivity)]
  have hcost : (M : ℝ) * b - k * l ≤ a * (b - l + X * (8 * R ^ 2)) := by
    linarith only [hq, herr, mul_le_mul_of_nonneg_left hbb (show 0 ≤ 4 * R by positivity),
      mul_le_mul_of_nonneg_right (show (M : ℝ) ≤ 2 * a by linarith) (show 0 ≤ 4 * R ^ 2 * X by positivity)]
  have hlog := le_of_mul_le_mul_left (hc.trans hcost) ha0
  have hsave : Real.log H / d ≤ l + T * X := (div_le_iff₀ hd0).mpr (by
    rw [add_mul, show l * d = Real.log L from div_mul_cancel₀ _ hd0.ne']
    linarith)
  apply Real.natCast_le_of_log_le_log (by omega) (by unfold auxMainTerm; positivity)
  rw [auxMainTerm, Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_div hA.ne' (by positivity), auxDegreeScale, Real.log_rpow hd0,
    Real.log_rpow (by linarith : 0 < B), Real.log_rpow hH]
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < (r : ℝ) * X)).mp
  dsimp only [hypersurfaceSmallHeightError, b, boxExponent, heightExponent, degreeRoot, X, R, r] at hlog hsave ⊢
  push_cast at hlog hsave ⊢
  linear_combination (norm := (field_simp; ring_nf; norm_num)) hlog + hsave

/-- A logarithmic bad-prime loss is absorbed by a linear height saving. -/
private lemma log_one_add_le_linear_add_log {x c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) :
    Real.log (1 + x) ≤ x / c + Real.log c := by
  have hc0 : 0 < c := by linarith
  have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (1 + x) / c)
  rw [Real.log_div (by positivity) hc0.ne', add_div] at hh
  linarith only [hh, (div_le_one hc0).mpr hc]

/-- Dimension-dependent error in the logarithmic degree bound at large height. -/
def hypersurfaceLargeHeightError (r : ℕ) (E T : ℝ) : ℝ :=
  Real.log (8 * (r : ℝ)) + (E + hypersurfaceRankLogError r + 2 * T) / r

/-- At large height the leading-coefficient saving absorbs both the height and bad-prime terms. -/
theorem hypersurface_large_height_degree_bound {r d M : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hM : 8 * d * (r + 1) ≤ M)
    (B L H E T : ℝ) (hL : 1 ≤ L) (hH : 1 ≤ H) (hT : 0 ≤ T)
    (hheight : 2 * d * (r + 1 : ℝ) * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log L + T * d * (d : ℝ) ^ (1 / (r : ℝ)))
    (hcomparison : NormalizedRankComparison r d M (Real.log B) (Real.log L)
      (Real.log (1 + Real.log H / (d : ℝ) ^ 2)) E) :
    (M : ℝ) ≤ Real.exp (hypersurfaceLargeHeightError r E T) * (d : ℝ) ^ (4 - 1 / (r : ℝ)) := by
  let X := (d : ℝ) ^ (1 / (r : ℝ))
  let b := (r + 1 : ℝ) * Real.log B
  let l := Real.log L / (d : ℝ)
  let h := Real.log H / (d : ℝ)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
  have hd0 : (0 : ℝ) < d := by positivity
  have hr0 : (0 : ℝ) < r := by positivity
  have hX : 0 < X := by positivity
  have hMd : 2 * d ≤ M := by nlinarith
  have hM' : 8 * (d : ℝ) * (r + 1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hl : 0 ≤ l := div_nonneg (Real.log_nonneg hL) hd0.le
  have hh : 0 ≤ h := div_nonneg (Real.log_nonneg hH) hd0.le
  obtain ⟨a, k, ha, ha', hk, hc⟩ := log_degree_comparison hrpos hd hMd hcomparison
  have hdM' : 2 * (d : ℝ) ≤ M := by exact_mod_cast hMd
  have ha0 : 0 < a := by linarith
  have ha₂ : a ≤ 2 * M := by nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hr0.le]
  have hk' : 3 * (M : ℝ) / 4 ≤ k := by linarith
  have hb : 2 * b ≤ h := (le_div_iff₀ hd0).mpr (by dsimp [b]; linarith)
  have hp : h ≤ l + T * X := (div_le_iff₀ hd0).mpr (by dsimp [l, X]; rw [add_mul, div_mul_cancel₀ _ hd0.ne']; linarith)
  have hlin : (M : ℝ) * b - k * l ≤ a * (2 * T * X - h / 8) := by
    linarith only [mul_le_mul_of_nonneg_right hk' hl,
      mul_le_mul_of_nonneg_left
        (show b - 3 * l / 4 ≤ T * X - h / 4 by linarith [show 0 ≤ T * X by positivity]) hM0,
      mul_le_mul_of_nonneg_right (show (M : ℝ) ≤ 2 * a by linarith) (show 0 ≤ T * X by positivity),
      mul_le_mul_of_nonneg_right ha₂ hh]
  have hlog' := le_of_mul_le_mul_left (hc.trans hlin) ha0
  have hXle : X ≤ d := (Real.rpow_le_rpow_of_exponent_le hd1 ((div_le_one hr0).mpr hr1)).trans_eq (Real.rpow_one _)
  have hcost := log_one_add_le_linear_add_log (div_nonneg (Real.log_nonneg hH) (sq_nonneg (d : ℝ)))
    (show 1 ≤ 8 * (r : ℝ) by linarith)
  have hcancel : (r : ℝ) * Real.log (1 + Real.log H / (d : ℝ) ^ 2) ≤
      r * Real.log (8 * (r : ℝ)) + h / (8 * X) := by
    have hdiv := div_le_div_of_nonneg_left hh (show 0 < 8 * X by positivity)
      (show 8 * X ≤ 8 * d by linarith)
    dsimp only [h] at hdiv ⊢
    linear_combination (norm := (field_simp; ring_nf; norm_num)) (r : ℝ) * hcost + hdiv
  apply Real.natCast_le_of_log_le_log (by omega) (by positivity)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_rpow hd0]
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < (r : ℝ) * X)).mp
  dsimp only [hypersurfaceLargeHeightError, X, h] at hlog' hcancel ⊢
  linear_combination (norm := (field_simp; ring_nf; norm_num)) hlog' + X * hcancel

end
end CCDN
