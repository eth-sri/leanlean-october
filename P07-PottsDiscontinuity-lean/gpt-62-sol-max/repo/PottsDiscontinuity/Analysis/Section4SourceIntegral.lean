module

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4TauIntegral

/-!
# The source-coordinate logarithmic derivative integral

This file transports the Abel-summed Fourier computation from the `α` coordinate to the
source coordinate `x = k(α)` using the substitution theorem for monotone maps.
-/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

/-- The source profile `ℓ(x) = log |M(e^{ix})|`, pulled back from the explicit `P` profile. -/
noncomputable def fourierEll (lam : ℝ) (x : ℝ) : ℝ :=
  fourierP lam (Bethe.kInv lam x)

/-- The source derivative representative obtained by differentiating `P = ℓ ∘ k` away from zero.
Its value at the logarithmic point is immaterial to interval integrals. -/
noncomputable def fourierEllPrime (lam : ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    fourierPPrime lam (Bethe.kInv lam x) / Bethe.Xi lam (Bethe.kInv lam x)

private theorem kInv_mem_Ioo {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) : Bethe.kInv lam x ∈ Ioo (-π) π := by
  have hIcc := Bethe.kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  have hαnePi : Bethe.kInv lam x ≠ π := by
    grind [Bethe.kMap_pi, Bethe.kMap_kInv]
  have hαneNegPi : Bethe.kInv lam x ≠ -π := by
    intro h
    have hx' := Bethe.kMap_kInv hlam x
    rw [h, Bethe.kMap_neg_pi] at hx'
    simp_all
  exact ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hαneNegPi),
    lt_of_le_of_ne hIcc.2 hαnePi⟩

private theorem kInv_ne_zero {lam x : ℝ} (hlam : 0 < lam) (hx : x ≠ 0) :
    Bethe.kInv lam x ≠ 0 := by
  intro h
  have := Bethe.kMap_kInv hlam x
  rw [h, Bethe.kMap_zero] at this
  exact hx this.symm

/-- Away from the logarithmic singularity, `fourierEll` has the source derivative. -/
theorem fourierEll_hasDerivAt {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    HasDerivAt (fourierEll lam) (fourierEllPrime lam x) x := by
  have hα := kInv_mem_Ioo hlam hx
  have hα0 := kInv_ne_zero hlam hx0
  have hP := fourierP_hasDerivAt hlam hα hα0
  have hki := Bethe.hasDerivAt_kInv hlam x
  have hcomp := hP.comp x hki
  have hderiv : fourierPPrime lam (Bethe.kInv lam x) *
      (Bethe.Xi lam (Bethe.kInv lam x))⁻¹ = fourierEllPrime lam x := by
    simp [fourierEllPrime, hx0, div_eq_mul_inv]
  aesop

/-- The profile fourierEll is the source logarithm log |M(e^(ix))| on the punctured
fundamental interval, with c² = 2 - 2Δ = 2 + 2 cosh λ. -/
theorem fourierEll_eq_log_norm {lam c x : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hx : x ∈ Ioo (-π) π)
    (hx0 : x ≠ 0) :
    fourierEll lam x = Real.log ‖BetheAnsatz.M c (Complex.exp (I * (x : ℂ)))‖ := by
  have hα := kInv_mem_Ioo hlam hx
  have hα0 := kInv_ne_zero hlam hx0
  have hcos : Real.cos (Bethe.kInv lam x) < 1 := by
    grind [Real.cos_le_one, Real.cos_eq_one_iff_of_lt_of_lt]
  calc
    fourierEll lam x = fourierP lam (Bethe.kInv lam x) := rfl
    _ = Real.log ‖BetheAnsatz.M c
        (Complex.exp (I * (Bethe.kMap lam (Bethe.kInv lam x) : ℂ)))‖ :=
      fourierP_eq_log_norm hlam hc hcos
    _ = Real.log ‖BetheAnsatz.M c (Complex.exp (I * (x : ℂ)))‖ := by
      rw [Bethe.kMap_kInv hlam]

/-- Substitute the increasing Bethe coordinate map in the logarithmic derivative integral. -/
theorem fourierEllPrime_tau_integral_eq_fourierPPrime {lam : ℝ} (hlam : 0 < lam) :
    ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
      ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := -π) (b := π) (g := fun x => fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x)
    (Bethe.continuous_kMap hlam).continuousOn (fun α _ => Bethe.hasDerivAt_kMap hlam α)
    (fun α _ => (Bethe.Xi_pos hlam α).le)
  rw [Bethe.kMap_neg_pi, Bethe.kMap_pi] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro α _
  by_cases hα : α = 0
  · subst α
    simp [fourierEllPrime, fourierPPrime, Bethe.kMap_zero]
  have hk : Bethe.kMap lam α ≠ 0 := fun he => hα ((Bethe.strictMono_kMap hlam).injective
    (he.trans (Bethe.kMap_zero lam).symm))
  have hl : Bethe.lamOf (-Real.cosh lam) = lam := (Bethe.eq_lamOf hlam (by simp)).symm
  simp only [Function.comp_apply, fourierEllPrime, hk, ite_false, Bethe.tau, hl,
    Bethe.kInv_kMap hlam]
  field_simp [(Bethe.Xi_pos hlam α).ne']

/-- The source-coordinate integral is exactly the correction term in (4.3), in the
ordered-partial-sum sense.  The limit `S` is the one from the alternating tanh series. -/
theorem fourierEllPrime_tau_integral_value {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      (Real.log (abs (-Real.cosh lam)) -
        (∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        lam + 2 * S) := by
  simpa [fourierEllPrime_tau_integral_eq_fourierPPrime hlam]
      using fourierPPrime_tauSeries_integral hlam

/-- The analytic exponent in the eigenvalue-ratio formula, with the source parameter
`Δ = -cosh λ` and positive real mode `r`. -/
theorem fourierRatioExponent {lam r : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      -r * Real.log (abs (-Real.cosh lam)) +
          r * (∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        -r * (lam + 2 * S) := by
  obtain ⟨S, hS, hvalue⟩ := fourierEllPrime_tau_integral_value hlam
  grind

end PottsDiscontinuity
