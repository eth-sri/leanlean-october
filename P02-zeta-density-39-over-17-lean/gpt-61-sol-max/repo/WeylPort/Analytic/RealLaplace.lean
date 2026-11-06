module
/- Extracted from pinned McColm source, MIT-0; see analytic-extraction.json. -/
public import Mathlib

@[expose] public section

-- Lean 4.34 elaborator compatibility; kernel checking stays enabled.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory
open scoped Topology Interval
namespace RiemannZeta.GuthMaynard
section
variable {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a)
include s hs a ha

/-- The elementary Gamma integral after a positive real dilation. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_eq
     :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Complex.exp (-(a * x))) =
      (1 / a : ℂ) ^ s * Gamma s := by
  exact Complex.integral_cpow_mul_exp_neg_mul_Ioi hs ha

/-- The dilated complex Gamma integrand is integrable on the positive
half-line. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi
     :
    IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp (-(a * x)))
      (Set.Ioi 0) := by
  let f : ℝ → ℂ := fun u => Complex.exp (-(u : ℂ))
  have hbase : MellinConvergent f s := by
    unfold MellinConvergent f
    refine (Complex.GammaIntegral_convergent hs).congr_fun ?_ measurableSet_Ioi
    intro x hx
    change ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (x : ℂ) ^ (s - 1) * Complex.exp (-(x : ℂ))
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  have hscaled :=
    (MellinConvergent.comp_mul_left (f := f) (s := s) ha).2 hbase
  unfold MellinConvergent at hscaled
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [f, smul_eq_mul, Complex.ofReal_mul]
end




