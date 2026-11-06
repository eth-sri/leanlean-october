module
import Mathlib
public import MathCollab.Density.DetectorTaylorFamily
public import Mathlib.Analysis.Analytic.Binomial

@[expose] public section

open Complex Filter
open scoped BigOperators Topology

namespace MathCollab.Density

section
variable (β : ℝ) (j : ℕ)
include β j

theorem detectorTaylorRatio_eq_prod_div  :
    detectorTaylorRatio β j = (∏ l ∈ Finset.range j, (β+(l : ℝ))) / (j.factorial : ℝ) := by
  unfold detectorTaylorRatio
  rw [Finset.prod_div_distrib]
  congr 1
  rw [Nat.factorial_eq_prod_range_add_one]
  push_cast
  apply Finset.prod_congr rfl
  bound

theorem detector_descPochhammer_neg  :
    (descPochhammer ℤ j).smeval (-β) =
      (-1 : ℝ)^j * ∏ l ∈ Finset.range j, (β+(l : ℝ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [descPochhammer_succ_right]
    simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, npow_one, npow_zero]
    rw [ih, Finset.prod_range_succ, pow_succ]
    ring

theorem choose_neg_eq_detectorTaylorRatio  :
    Ring.choose (-β) j = (-1 : ℝ)^j * detectorTaylorRatio β j := by
  rw [Ring.choose_eq_smul, detector_descPochhammer_neg, detectorTaylorRatio_eq_prod_div]
  ring
end


/-- Exact binomial expansion at every positive block coordinate. -/
theorem hasSum_detector_binomial {β x : ℝ} (hx : 1 ≤ x) (hx' : x ≤ 2) :
    HasSum (fun j : ℕ => detectorTaylorWeight β j*(2*x-3)^j)
      ((2*x/3)^(-β)) := by
  let z : ℝ := (2*x-3)/3
  have hz : |z| < 1 := by dsimp [z]; rw [abs_lt]; constructor <;> linarith
  have he : z ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Real.dist_eq] using hz
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -β)).hasSum_sub he
  simp only [sub_zero, binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at h
  have hc : ∀ j : ℕ, Ring.choose (-β) j*z^j = detectorTaylorWeight β j*(2*x-3)^j := by
    intro j
    rw [choose_neg_eq_detectorTaylorRatio, detectorTaylorWeight]
    dsimp [z]
    rw [div_pow, div_pow]
    ring
  have hh : 1+z = 2*x/3 := by dsimp [z]; ring
  simpa only [hc, hh] using h


