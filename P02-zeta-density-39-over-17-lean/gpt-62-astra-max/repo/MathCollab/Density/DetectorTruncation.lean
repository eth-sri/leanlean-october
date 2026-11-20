module
public import MathCollab.Density.DetectorError

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The original summand, with the n=0 coefficient equal to zero. -/
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


/-- The reciprocal geometric denominator costs at most 2T for T>=1. -/
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

/-- The original logarithmic cutoff, with terms retained for n<K. -/
def firstDetectorCutoff (T : ℝ) : ℕ := ⌈T*(Real.log T)^2⌉₊



end MathCollab.Density
