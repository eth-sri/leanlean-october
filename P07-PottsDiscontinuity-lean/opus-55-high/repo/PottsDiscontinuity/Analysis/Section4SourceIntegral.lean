module

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4TauIntegral

/-!
# The source-coordinate logarithmic derivative integral

This file transports the Abel-summed Fourier computation from the `α` coordinate to the
source coordinate `x = k(α)`.  The logarithmic point is handled by splitting the substitution
at zero; the literal and continuous representatives of `τ` agree almost everywhere.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

section
variable (lam : ℝ) (x : ℝ)
/-- The source profile `ℓ(x) = log |M(e^{ix})|`, pulled back from the explicit `P` profile. -/
def fourierEll  : ℝ :=
  fourierP lam (Bethe.kInv lam x)

/-- The source derivative representative obtained by differentiating `P = ℓ ∘ k` away from zero.
Its value at the logarithmic point is immaterial to interval integrals. -/
def fourierEllPrime  : ℝ :=
  if x = 0 then 0 else
    fourierPPrime lam (Bethe.kInv lam x) / Bethe.Xi lam (Bethe.kInv lam x)
end

section
variable {lam x : ℝ} (hlam : 0 < lam)
include hlam
theorem kInv_mem_Ioo (hx : x ∈ Ioo (-π) π) : Bethe.kInv lam x ∈ Ioo (-π) π := by
  have h := Bethe.kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  have := Bethe.kMap_kInv hlam x
  refine ⟨h.1.lt_of_ne fun h' => ?_, h.2.lt_of_ne fun h' => ?_⟩
  · rw [← h', Bethe.kMap_neg_pi] at this
    linarith [hx.1]
  · rw [h', Bethe.kMap_pi] at this
    linarith [hx.2]

theorem kInv_ne_zero (hx : x ≠ 0) :
    Bethe.kInv lam x ≠ 0 := by
  intro h
  have := Bethe.kMap_kInv hlam x
  rw [h, Bethe.kMap_zero] at this
  simp_all

/-- Away from the logarithmic singularity, `fourierEll` has the source derivative. -/
theorem fourierEll_hasDerivAt (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    HasDerivAt (fourierEll lam) (fourierEllPrime lam x) x :=
  ((fourierP_hasDerivAt hlam (kInv_mem_Ioo hlam hx) (kInv_ne_zero hlam hx0)).comp x
    ((Bethe.hasDerivAt_kMap hlam _).of_local_left_inverse (Bethe.continuous_kInv hlam).continuousAt
      (Bethe.Xi_pos hlam _).ne' (.of_forall (Bethe.kMap_kInv hlam)))).congr_deriv
    (by simp [fourierEllPrime, hx0, div_eq_mul_inv])

/-- The profile fourierEll is the source logarithm log |M(e^(ix))| on the punctured
fundamental interval, with c² = 2 - 2Δ = 2 + 2 cosh λ. -/
theorem fourierEll_eq_log_norm {c : ℝ}
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hx : x ∈ Ioo (-π) π)
    (hx0 : x ≠ 0) :
    fourierEll lam x = Real.log ‖BetheAnsatz.M c (Complex.exp (I * (x : ℂ)))‖ := by
  have hα := kInv_mem_Ioo hlam hx
  rw [fourierEll, fourierP_eq_log_norm hlam hc ((Real.cos_le_one _).lt_of_ne fun h => kInv_ne_zero hlam hx0
    ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hα.1, pi_pos]) (by linarith [hα.2, pi_pos])).1 h)),
    Bethe.kMap_kInv hlam]
end

/-- The analytic exponent in the eigenvalue-ratio formula, with the source parameter
`Δ = -cosh λ` and positive real mode `r`.  It follows by the change of variables `x = k(α)`
and the value of the α-integral of `P′ τ`. -/
theorem fourierRatioExponent {lam r : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      -r * Real.log (abs (-Real.cosh lam)) +
          r * (∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        -r * (lam + 2 * S) := by
  obtain ⟨S, hS, hCorr⟩ := fourierPPrime_tauSeries_integral hlam
  obtain ⟨S', hS', hIdentity⟩ := identity43 lam hlam
  have himg :=
    (Bethe.mapsTo_kMap hlam).image_subset.antisymm fun x hx =>
      ⟨_, Bethe.kInv_mem_Icc hlam hx, Bethe.kMap_kInv hlam x⟩
  have hsub := integral_image_eq_integral_abs_deriv_smul (measurableSet_Icc (a := -π) (b := π))
    (fun α _ => (Bethe.hasDerivAt_kMap hlam α).hasDerivWithinAt)
    (Bethe.strictMono_kMap hlam).injective.injOn
    (fun x => fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x)
  rw [himg] at hsub
  have hint : ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
      ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α := by
    rw [intervalIntegral.integral_of_le (by linarith [pi_pos]),
      intervalIntegral.integral_of_le (by linarith [pi_pos]), ← integral_Icc_eq_integral_Ioc,
      ← integral_Icc_eq_integral_Ioc, hsub]
    refine setIntegral_congr_fun measurableSet_Icc fun α _ => ?_
    rw [abs_of_pos (Bethe.Xi_pos hlam α), smul_eq_mul, Bethe.tau, ← Bethe.eq_lamOf hlam (by simp),
      Bethe.kInv_kMap hlam, fourierEllPrime, Bethe.kInv_kMap hlam]
    by_cases h : α = 0
    · simp [h, Bethe.kMap_zero, fourierPPrime]
    · rw [ite_eq_right fun h' => h ((Bethe.strictMono_kMap hlam).injective (h'.trans (Bethe.kMap_zero lam).symm))]
      field_simp [(Bethe.Xi_pos hlam α).ne']
  refine ⟨S, hS, ?_⟩
  rw [tendsto_nhds_unique hS hS', hint, abs_neg, abs_of_pos (Real.cosh_pos lam),
    ← tendsto_nhds_unique (tendsto_const_nhds.sub hCorr) hIdentity]
  ring

end PottsDiscontinuity
