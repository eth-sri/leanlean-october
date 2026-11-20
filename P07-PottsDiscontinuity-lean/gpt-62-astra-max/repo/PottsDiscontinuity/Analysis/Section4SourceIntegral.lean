module

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4TauIntegral

/-!
# The source-coordinate logarithmic derivative integral

This file transports the Abel-summed Fourier computation from the `α` coordinate to the
source coordinate `x = k(α)`.  We use monotone change of variables directly with the literal series.
-/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

section
variable (lam : ℝ) (x : ℝ)
include lam x

/-- The source profile `ℓ(x) = log |M(e^{ix})|`, pulled back from the explicit `P` profile. -/
noncomputable def fourierEll : ℝ :=
  fourierP lam (Bethe.kInv lam x)

/-- The source derivative representative obtained by differentiating `P = ℓ ∘ k` away from zero.
Its value at the logarithmic point is immaterial to interval integrals. -/
noncomputable def fourierEllPrime : ℝ :=
  if x = 0 then 0 else
    fourierPPrime lam (Bethe.kInv lam x) / Bethe.Xi lam (Bethe.kInv lam x)

end

section
variable {lam x : ℝ} (hlam : 0 < lam) (hx : x ∈ Ioo (-π) π)
include hlam

include hx in
private theorem kInv_mem_Ioo : Bethe.kInv lam x ∈ Ioo (-π) π := by
  have hIcc := Bethe.kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  have hαnePi : Bethe.kInv lam x ≠ π := by
    intro h
    have hx' := Bethe.kMap_kInv hlam x
    simp_all [h, Bethe.kMap_pi]
  have hαneNegPi : Bethe.kInv lam x ≠ -π := by
    intro h
    have hx' := Bethe.kMap_kInv hlam x
    simp_all [h, Bethe.kMap_neg_pi]
  grind

private theorem kInv_ne_zero (hx : x ≠ 0) :
    Bethe.kInv lam x ≠ 0 := by
  intro h
  have := Bethe.kMap_kInv hlam x
  simp_all [h, Bethe.kMap_zero]

/-- The inverse map has derivative `1 / Ξ_λ(k⁻¹(x))`. -/
private theorem hasDerivAt_kInv_of_kMap :
    HasDerivAt (Bethe.kInv lam)
      ((Bethe.Xi lam (Bethe.kInv lam x))⁻¹) x := by
  let α := Bethe.kInv lam x
  have hki :=
    (Bethe.analyticAt_kInv hlam x).differentiableAt
  have hc := (Bethe.hasDerivAt_kMap hlam α).comp x hki.hasDerivAt
  let product := Bethe.Xi lam α * deriv (Bethe.kInv lam) x
  have hcomp : HasDerivAt (fun y : ℝ => y)
      (product) x := by
    have hfun :=
      funext (Bethe.kMap_kInv hlam)
    change HasDerivAt (fun y : ℝ => Bethe.kMap lam (Bethe.kInv lam y))
      (product) x at hc
    grind
  have hprod : product = 1 := by
    have := hcomp.deriv
    simpa using this.symm
  have hderiv : deriv (Bethe.kInv lam) x = (Bethe.Xi lam α)⁻¹ := by
    grind
  convert hki.hasDerivAt.congr_deriv hderiv using 1

include hx in
/-- Away from the logarithmic singularity, `fourierEll` has the source derivative. -/
theorem fourierEll_hasDerivAt (hx0 : x ≠ 0) :
    HasDerivAt (fourierEll lam) (fourierEllPrime lam x) x := by
  have hcomp := (fourierP_hasDerivAt hlam (kInv_mem_Ioo hlam hx) (kInv_ne_zero hlam hx0)).comp x (hasDerivAt_kInv_of_kMap hlam)
  have hderiv : fourierPPrime lam (Bethe.kInv lam x) *
      (Bethe.Xi lam (Bethe.kInv lam x))⁻¹ = fourierEllPrime lam x := by
    simp [fourierEllPrime, hx0, div_eq_mul_inv]
  change HasDerivAt (fourierP lam ∘ Bethe.kInv lam) (fourierEllPrime lam x) x
  grind

end

/-- The profile fourierEll is the source logarithm log |M(e^(ix))| on the punctured
fundamental interval, with c² = 2 - 2Δ = 2 + 2 cosh λ. -/
theorem fourierEll_eq_log_norm {lam c x : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hx : x ∈ Ioo (-π) π)
    (hx0 : x ≠ 0) :
    fourierEll lam x = Real.log ‖BetheAnsatz.M c (Complex.exp (I * x))‖ := by
  have hα := kInv_mem_Ioo hlam hx
  have hα0 := kInv_ne_zero hlam hx0
  calc
    _ = fourierP lam (Bethe.kInv lam x) := rfl
    _ = Real.log ‖BetheAnsatz.M c
        (Complex.exp (I * (Bethe.kMap lam (Bethe.kInv lam x))))‖ :=
      fourierP_eq_log_norm hlam hc (by
        have hne : Real.cos (Bethe.kInv lam x) ≠ 1 := by
          intro h
          have hαbounds : -(2 * π) < Bethe.kInv lam x ∧ Bethe.kInv lam x < 2 * π := by
            grind
          have hperiod := (Real.cos_eq_one_iff_of_lt_of_lt hαbounds.1 hαbounds.2).mp h
          grind
        exact lt_of_le_of_ne (Real.cos_le_one _) hne)
    _ = _ := by
      rw [Bethe.kMap_kInv hlam]

section
variable {lam : ℝ} (hlam : 0 < lam)
include hlam

/-- Monotone change of variables does not require continuity of the integrand
at the logarithmic point. Pull the literal series back along `kMap` directly. -/
theorem fourierEllPrime_tau_integral_eq_fourierPPrime :
    ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
      ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α := by
  have h := integral_comp_mul_deriv_of_deriv_nonneg (a := -π) (b := π)
    (g := fun x => fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x)
    (Bethe.continuous_kMap hlam).continuousOn (fun α _ => Bethe.hasDerivAt_kMap hlam α)
    (fun α _ => (Bethe.Xi_pos hlam α).le)
  rw [Bethe.kMap_neg_pi, Bethe.kMap_pi] at h
  rw [← h]
  apply integral_congr
  intro α _
  simp only [Function.comp_apply, fourierEllPrime, Bethe.tau,
    ← Bethe.eq_lamOf hlam (show Real.cosh lam = -(-Real.cosh lam) by simp), Bethe.kInv_kMap hlam]
  by_cases hz : α = 0
  · simp [hz, fourierPPrime]
  · rw [if_neg (by rw [← Bethe.kMap_zero lam]; exact (Bethe.strictMono_kMap hlam).injective.ne hz)]
    field_simp [(Bethe.Xi_pos hlam α).ne']

/-- The source-coordinate integral is exactly the correction term in (4.3), in the
ordered-partial-sum sense.  The limit `S` is the one from the alternating tanh series. -/
theorem fourierEllPrime_tau_integral_value :
    ∃ S,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      (Real.log (abs (-Real.cosh lam)) -
        (∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        lam + 2 * S) := by
  obtain ⟨S, hS, hCorr⟩ := fourierPPrime_tauSeries_integral hlam
  obtain ⟨S', hS', hIdentity⟩ := identity43 lam hlam
  have hSS' := tendsto_nhds_unique hS hS'
  refine ⟨S, hS, ?_⟩
  have hlog : Real.log (abs (-Real.cosh lam)) = Real.log (Real.cosh lam) := by
    simp
  rw [(fourierEllPrime_tau_integral_eq_fourierPPrime hlam), hlog]
  have hEq := tendsto_nhds_unique (tendsto_const_nhds.sub hCorr) hIdentity
  linarith

end

/-- The analytic exponent in the eigenvalue-ratio formula, with the source parameter
`Δ = -cosh λ` and positive real mode `r`. -/
theorem fourierRatioExponent {lam r : ℝ} (hlam : 0 < lam) :
    ∃ S,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      -r * Real.log (abs (-Real.cosh lam)) +
          r * (∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        -r * (lam + 2 * S) := by
  obtain ⟨S, hS, hvalue⟩ := fourierEllPrime_tau_integral_value hlam
  grind

end PottsDiscontinuity
