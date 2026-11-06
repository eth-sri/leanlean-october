/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsCircleAverage
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.GMC.GaussianCovariance
public import DOZZ.Statements.GMC.IsGaussianL2Limit
public import DOZZ.GFFStructure.CircleVersion

/-! Continuity of the circle covariance potential for every Gaussian L² limit. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
section
variable (hX : IsEquatorGFF P X)
include hX

private theorem gaussianL2Limit_mean_zero
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) :
    (∫ ω, L ω ∂P) = 0 := by
  let _ := hX.1
  obtain ⟨hLmem, f, hLapprox⟩ := hL
  have hcomm : ∀ n,
      eLpNorm (fun ω => X ω (f n) - L ω) 2 P =
        eLpNorm (fun ω => L ω - X ω (f n)) 2 P := by
    intro n
    exact eLpNorm_sub_comm ..
  have happrox : Tendsto
      (fun n => eLpNorm (fun ω => X ω (f n) - L ω) 2 P) atTop (𝓝 0) := by
    simp_all
  exact integral_eq_zero_of_eLpNorm_sub
    (fun n => equatorGFF_test_memLp X hX (f n)) hLmem
    (fun n => equatorGFF_test_integral X hX (f n)) happrox

/-- For each fixed circle radius, covariance against any Gaussian `L²` limit is a continuous
function of the center. -/
theorem continuous_gaussianCovariance_circle_of_IsGaussianL2Limit
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) (r : ℝ) :
    Continuous (fun x => gaussianCovariance P (fun ω => Xc ω x r) L) := by
  let _ := hX.1
  let W := hL.1.toLp L
  have hmeanL := gaussianL2Limit_mean_zero P X hX L hL
  have hmeanCircle (x : ℂ) : (∫ ω, Xc ω x r ∂P) = 0 :=
    (circleAverage_isGaussianProcess P X Xc hX hXc).2 x r
  have hpair (x : ℂ) :
      gaussianCovariance P (fun ω => Xc ω x r) L =
        inner ℝ (circleAverageL2 hXc (x, r)) W := by
    have hcov :
      gaussianCovariance P (fun ω => Xc ω x r) L =
          covariance (fun ω => Xc ω x r) L P := by
      unfold gaussianCovariance
      rw [covariance_eq_sub (hXc.2.1 x r) hL.1, hmeanCircle x, hmeanL]
      simp
    rw [hcov]
    rw [← covariance_congr_ae (circleAverageL2_ae_eq hXc (x, r))
      (MemLp.coeFn_toLp hL.1)]
    rw [covariance_L2_eq]
    have hmeanW : (∫ ω, W ω ∂P) = 0 := by
      rw [← hmeanL]
      exact integral_congr_ae (MemLp.coeFn_toLp hL.1)
    aesop
  have hparam : Continuous (fun x : ℂ => (x, r)) :=
    continuous_id.prodMk continuous_const
  have hcircle : Continuous (fun x => circleAverageL2 hXc (x, r)) :=
    (continuous_circleAverageL2 P X Xc hX hXc).comp hparam
  simpa only [hpair] using hcircle.inner continuous_const

end

end

end DOZZ.Proofs
