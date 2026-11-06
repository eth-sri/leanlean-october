module
import Mathlib
public import MathCollab.Density.DetectorError

@[expose] public section

open Complex MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace MathCollab.Density

/- The original summand, with the n=0 coefficient equal to zero. -/
def detectorTerm (ρ : ℂ) (X T : ℝ) (n : ℕ) : ℂ :=
  (mollifierCoefficient X n : ℂ)*(n : ℂ)^(-ρ)*(Real.exp (-(n : ℝ)/T) : ℂ)

theorem norm_detectorTerm_le {ρ : ℂ} (X : ℝ) {T : ℝ} (n : ℕ)
    (hρ : 0 ≤ ρ.re) :
    ‖detectorTerm ρ X T n‖ ≤ (⌊X⌋₊ : ℝ)*Real.exp (-(n : ℝ)/T) := by
  rw [detectorTerm, ← smoothedDetector_term_eq ρ X T n, norm_mul, Complex.norm_exp]
  have he : (-((n : ℝ)*(1/T : ℝ)) : ℂ).re = -(n : ℝ)/T := by
    simp only [← Complex.ofReal_mul,
      ← Complex.ofReal_neg, Complex.ofReal_re]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (norm_mollifier_LSeries_term_le_cutoff X n hρ) (by positivity)

/- A tail estimate uniform in both coordinates of rho on Re(rho)>=0. -/
theorem norm_detector_tail_le {ρ : ℂ} (X : ℝ) {T : ℝ} (K : ℕ)
    (hT : 0 < T) (hρ : 0 ≤ ρ.re) :
    ‖∑' n : ℕ, detectorTerm ρ X T (n+K)‖ ≤
      (⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/T)*(1-Real.exp (-1/T))⁻¹ := by
  let r := Real.exp (-1/T)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hT)
  have hg := (hasSum_geometric_of_lt_one hr hr').mul_left
    ((⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/T))
  have hb : ∀ n : ℕ, ‖detectorTerm ρ X T (n+K)‖ ≤
      (⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/T)*r^n := by
    intro n
    have he : Real.exp (-((n+K : ℕ) : ℝ)/T) = Real.exp (-(K : ℝ)/T)*r^n := by
      rw [← Real.exp_nat_mul]
      rw [← Real.exp_add]
      grind
    exact (norm_detectorTerm_le X (n+K) hρ).trans_eq (by rw [he]; ring)
  have hn := hg.summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hb hg.summable).trans_eq hg.tsum_eq)

/- The reciprocal geometric denominator costs at most 2T for T>=1. -/
theorem detector_geometric_factor_le {T : ℝ} (hT : 1 ≤ T) :
    (1-Real.exp (-1/T))⁻¹ ≤ 2*T := by
  have hTpos : 0 < T := by linarith
  have he := Real.add_one_le_exp (1/T)
  have hp : 0 < Real.exp (1/T) := Real.exp_pos _
  have hq : Real.exp (-1/T) = (Real.exp (1/T))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  have hd : 0 < 1-Real.exp (-1/T) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hTpos))
  rw [← one_div]
  apply (div_le_iff₀ hd).2
  rw [hq]
  have hmul : (1/T+1)*T ≤ Real.exp (1/T)*T := mul_le_mul_of_nonneg_right he hTpos.le
  have hone : (1/T+1)*T = 1+T := by field_simp
  rw [hone] at hmul
  have hinv : Real.exp (1/T)*(Real.exp (1/T))⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have hmul' := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hp.le)
  nlinarith [mul_nonneg (show 0 ≤ T-1 by linarith) (show 0 ≤ 1-(Real.exp (1/T))⁻¹ by simpa [hq] using hd.le)]

/- The original logarithmic cutoff, with terms retained for n<K. -/
def firstDetectorCutoff (T : ℝ) : ℕ := ⌈T*(Real.log T)^2⌉₊






