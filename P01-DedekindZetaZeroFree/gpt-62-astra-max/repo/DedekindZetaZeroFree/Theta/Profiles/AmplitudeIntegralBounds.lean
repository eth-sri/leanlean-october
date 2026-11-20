module

public import DedekindZetaZeroFree.Theta.Profiles.InducedAmplitudeDerivativeBounds

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ThetaArchInducedMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxRotatedKernelEstimates
open MeasureTheory

variable (β κ : ℂˣ) (f : PrincipalSeries positiveParameter) (hf : HasInducedAmplitudeEstimates β κ f)

include hf in
lemma exists_integrable_norm_amplitudeDerivative_le (j h : ℕ) (hj : j ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℂˣ) (ρ : ℝ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
      Integrable (fun x : ℂ => ‖amplitudeDerivative β κ f u j h ρ x‖) euclideanArea ∧
      (∫ x : ℂ, ‖amplitudeDerivative β κ f u j h ρ x‖ ∂euclideanArea) ≤
        C * ρ ^ ((2 / 3 : ℝ) - (h : ℝ)) := by
  obtain ⟨C, _, hb⟩ := hf.2.1 j h hj
  let D := C * (∫ x : ℂ, (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2) ∂euclideanArea)
  refine ⟨max 1 D, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u ρ hu hρ
  have hi' := integral_bound_of_rationalEnvelope h ρ C hρ _ ((hf.2.2 j h hj u ρ hu hρ).1).aestronglyMeasurable
    (fun x => by simpa [rationalEnvelope, mul_assoc] using hb u ρ x hu hρ)
  refine ⟨hi'.1, hi'.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right 1 D) (Real.rpow_nonneg hρ.le _)

include hf in
lemma exists_integrable_amplitudeDerivative_dominator (j : ℕ) (hj : j ≤ 2)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℂ → ℝ, Integrable B euclideanArea ∧
      ∀ (u : ℂˣ) (ρ : ℝ) (x : ℂ), ‖(u : ℂ)‖ = 1 → ρ ∈ Set.Icc a b →
        ‖amplitudeDerivative β κ f u j 0 ρ x‖ ≤ B x := by
  obtain ⟨C, hC, hb⟩ := hf.2.1 j 0 hj
  let D := C * b ^ (4 / 3 : ℝ) / a ^ (4 / 3 : ℝ)
  refine ⟨fun x => D * rationalEnvelope 0 a x,
    (rationalEnvelope_integrable 0 a ha).const_mul D, ?_⟩
  intro u ρ x hu hρ
  have hp := ha.trans_le hρ.1
  calc
    _ ≤ C * ρ ^ (4 / 3 : ℝ) * (ρ ^ 2 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
      simpa using hb u ρ x hu hp
    _ ≤ C * b ^ (4 / 3 : ℝ) * (a ^ 2 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.le hρ.2 (by norm_num)) hC.le) (Real.rpow_le_rpow_of_nonpos (by positivity) (by
        nlinarith [hρ.1]) (by norm_num))
        (Real.rpow_nonneg (by positivity) _)
        (mul_nonneg hC.le (Real.rpow_nonneg (ha.trans_le hab).le _))
    _ = D * rationalEnvelope 0 a x := by
      simp only [D, rationalEnvelope, Nat.cast_zero, zero_div, sub_zero]
      field_simp [(Real.rpow_pos_of_pos ha (4 / 3 : ℝ)).ne']

include hf in
lemma exists_norm_integral_exp_mul_amplitudeDerivative_le (j h : ℕ) (hj : j ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℂˣ) (ρ : ℝ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
      ‖∫ x : ℂ, Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
          amplitudeDerivative β κ f u j h ρ x ∂euclideanArea‖ ≤
        C * ρ ^ ((2 / 3 : ℝ) - (h : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := exists_integrable_norm_amplitudeDerivative_le β κ f hf j h hj
  refine ⟨C, hC, ?_⟩
  intro u ρ hu hρ
  calc
    _ ≤ ∫ x : ℂ, ‖Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
        amplitudeDerivative β κ f u j h ρ x‖ ∂euclideanArea := norm_integral_le_integral_norm _
    _ = ∫ x : ℂ, ‖amplitudeDerivative β κ f u j h ρ x‖ ∂euclideanArea := by
      congr 1
      ext x
      simp [Complex.norm_exp, Complex.mul_re]
    _ ≤ _ := (hb u ρ hu hρ).2

end DedekindZetaZeroFree.ThetaArchInducedMajorant

end
