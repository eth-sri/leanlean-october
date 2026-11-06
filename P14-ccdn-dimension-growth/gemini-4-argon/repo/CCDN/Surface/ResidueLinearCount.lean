/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.ResidueCover
import CCDN.Surface.PrimeWindowSubpower
import Mathlib.Algebra.Order.Star.Real

/-! A degree-dependent logarithmic prime window discharges all height
conditions of the surface residue cover. Its complete residual point count
is O(B), uniformly in coefficients, auxiliaries and initial curve families. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The constant `4 log (d + 1) + K + d + 2` scaling the logarithmic prime window of the residue
cover for a surface of degree `d` with logarithmic height constant `K`. -/
def surfaceResidueWindowScale (d : ℕ) (K : ℝ) : ℝ :=
  4 * Real.log ((d : ℝ) + 1) + K + d + 2

/-- The logarithmic size `surfaceResidueWindowScale d K * (log B + 1)` of the prime window of
the residue cover for a surface of degree `d` in the box of radius `B`. -/
def surfaceResidueWindow (d : ℕ) (K B : ℝ) : ℝ :=
  surfaceResidueWindowScale d K * (Real.log B + 1)

/-- The constant `1 + (log 4 + 4) c s`, with `c` the constant `scalingPrimeRatio` and `s` the
window scale `surfaceResidueWindowScale d K`, by which the logarithmic budget of the residue
cover is a multiple of `log B + 1`. -/
def surfaceResidueLogScale (d : ℕ) (K : ℝ) : ℝ :=
  1 + (Real.log 4 + 4) * scalingPrimeRatio * surfaceResidueWindowScale d K

/-- For `K ≥ 0`, the window scale `surfaceResidueWindowScale d K` is at least two. -/
theorem surfaceResidueWindowScale_two_le (d : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    2 ≤ surfaceResidueWindowScale d K := by
  have hh := Real.log_nonneg (show (1 : ℝ) ≤ (d : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) d])
  unfold surfaceResidueWindowScale
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- For `K ≥ 0` and `B ≥ 1`, the prime window size `surfaceResidueWindow d K B` is at
least one. -/
theorem surfaceResidueWindow_one_le (d : ℕ) {K B : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) :
    1 ≤ surfaceResidueWindow d K B := by
  have hscale := surfaceResidueWindowScale_two_le d hK
  have hlog := Real.log_nonneg hB
  unfold surfaceResidueWindow
  nlinarith

/-- For `K ≥ 0`, the budget constant `surfaceResidueLogScale d K` is at least one. -/
theorem surfaceResidueLogScale_one_le (d : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    1 ≤ surfaceResidueLogScale d K := by
  have hs := surfaceResidueWindowScale_two_le d hK
  have hp := scalingPrimeRatio_one_le
  have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  unfold surfaceResidueLogScale
  linarith [show 0 ≤ (Real.log 4 + 4) * scalingPrimeRatio * surfaceResidueWindowScale d K by positivity]

/-- For the prime window `surfaceResidueWindow d K B`, the logarithmic budget of the residue
cover equals `surfaceResidueLogScale d K * (log B + 1)`. -/
theorem surfaceResidueLogBudget_window (d : ℕ) (K B : ℝ) :
    surfaceResidueLogBudget B (surfaceResidueWindow d K B) =
      surfaceResidueLogScale d K * (Real.log B + 1) := by
  unfold surfaceResidueLogBudget surfaceResidueWindow surfaceResidueLogScale
  ring

/-- For a surface equation of degree `d ≥ 1` whose coefficients are bounded by `H ≥ 1` with
`log H ≤ K (log B + 1)`, the chosen window `surfaceResidueWindow d K B` and the cutoff
`2 B^(1/√d)` are residue-cover parameters. -/
theorem isSurfaceResidueWindow_of_log_height {f : MvPolynomial (Fin 3) ℤ}
    (hd : 1 ≤ f.totalDegree) {K B H : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    IsSurfaceResidueWindow f B H (surfaceResidueWindow f.totalDegree K B)
      (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) := by
  let d := f.totalDegree
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  have hlogd := Real.log_nonneg (show (1 : ℝ) ≤ (d : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hdR : (1 : ℝ) ≤ d := mod_cast hd
  have hroot1 : 1 / Real.sqrt (d : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one (Real.le_sqrt_of_sq_le (by simpa using hdR))
  have hp : 1 ≤ B ^ (1 / Real.sqrt (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  refine ⟨hB, hH, surfaceResidueWindow_one_le _ hK hB, hcoeff,
    by unfold surfaceResidueWindow surfaceResidueWindowScale; nlinarith,
    by linarith, by linarith, ?_⟩
  rw [← Real.exp_log (show 0 < 2 * B ^ (1 / Real.sqrt (d : ℝ)) by positivity), Real.exp_le_exp,
    Real.log_mul (by norm_num) (by positivity), Real.log_rpow hB0]
  unfold surfaceResidueWindow
  nlinarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2),
    surfaceResidueWindowScale_two_le d hK,
    mul_le_mul_of_nonneg_right hroot1 hlogB]

/-- The residual locus has a uniform linear count. The constant is
chosen before the equation, radius, congruence auxiliaries and curve family. -/
theorem surface_residue_linear_count (d : ℕ) (hd : 5 ≤ d)
    (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ), f.totalDegree = d →
      ∀ B : ℝ, ∀ hB : 1 ≤ B, ∀ F : SurfaceCongruenceFamily f B A,
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f) →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
      (∀ I ∈ S, IsSurfaceCurve (MvPolynomial.map (Int.castRingHom ℚ) f) I (δ I)) →
      (count (surfaceResidueResidualLocus F S (surfaceResidueWindow d K B)
        (2 * B ^ (1 / Real.sqrt (d : ℝ))) (surfaceResidueWindow_one_le d hK hB)) B : ℝ) ≤
          C * B := by
  have hscale := surfaceResidueWindowScale_two_le d hK
  have hlogscale := surfaceResidueLogScale_one_le d hK
  have hratio := scalingPrimeRatio_one_le
  have hdR : (5 : ℝ) ≤ d := mod_cast hd
  let U := scalingPrimeRatio * surfaceResidueWindowScale d K + 1
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  obtain ⟨C₀, hC₀, hbound⟩ := congruencePrimeWindow_surface_residual_bound
    (by linarith : 1 ≤ surfaceResidueWindowScale d K) (by linarith : 1 ≤ 2 * (d : ℝ)) 4
  let E := 8 * (d : ℝ) * A ^ 2 * (surfaceResidueLogScale d K) ^ 2 * U ^ 2
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨E * C₀ + 1, by positivity, ?_⟩
  intro f hfd B hB F hir S δ hS
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  have hL := surfaceResidueWindow_one_le d hK hB
  have hpoly := surface_residue_residual_count_le F hA hB hL
    (by omega : 1 ≤ f.totalDegree)
    (show 0 ≤ 2 * B ^ (1 / Real.sqrt (d : ℝ)) by positivity)
    (by rw [hfd]; nlinarith [Real.rpow_pos_of_pos hB0 (1 / Real.sqrt (d : ℝ))])
    hir S δ hS
  have hx : (2 * B ^ (1 / Real.sqrt (d : ℝ))) ^ 2 = 4 * B ^ (2 / Real.sqrt (d : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (B ^ (1 / Real.sqrt (d : ℝ))) 2, ← Real.rpow_mul hB0.le]
    norm_num only [Nat.cast_ofNat]; congr 2; ring
  rw [hfd, surfaceResidueLogBudget_window, hx] at hpoly
  have hu : scalingPrimeRatio * surfaceResidueWindow d K B + 1 ≤ U * (Real.log B + 1) := by
    dsimp only [surfaceResidueWindow, U]; nlinarith
  have hestimate :
      (count (surfaceResidueResidualLocus F S (surfaceResidueWindow d K B)
        (2 * B ^ (1 / Real.sqrt (d : ℝ))) hL) B : ℝ) ≤
      E * (((congruencePrimeWindow (surfaceResidueWindow d K B)).card *
        (2 * (d : ℝ)) ^ (congruencePrimeWindow (surfaceResidueWindow d K B)).card) *
        B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 4) := calc
    _ ≤ _ := hpoly
    _ ≤ 2 * (d : ℝ) * A ^ 2 * (surfaceResidueLogScale d K * (Real.log B + 1)) ^ 2 *
        (U * (Real.log B + 1)) ^ 2 * (4 * B ^ (2 / Real.sqrt (d : ℝ))) *
        (congruencePrimeWindow (surfaceResidueWindow d K B)).card *
        (2 * (d : ℝ)) ^ (congruencePrimeWindow (surfaceResidueWindow d K B)).card := by gcongr
    _ = _ := by dsimp only [E]; ring
  nlinarith [hestimate.trans (mul_le_mul_of_nonneg_left (hbound d hd B hB) hE)]

end
end CCDN
