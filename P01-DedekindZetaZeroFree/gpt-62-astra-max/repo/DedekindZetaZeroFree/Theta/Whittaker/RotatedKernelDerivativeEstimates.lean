module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxQuadraticKernelDerivatives

noncomputable def radialOp (F : ℝ → ℂ → ℂ) : ℝ → ℂ → ℂ :=
  fun ρ x => ((ρ / 2 : ℝ) : ℂ) * deriv (fun r : ℝ => F r x) ρ

end DedekindZetaZeroFree.KPCplxQuadraticKernelDerivatives

end

section

namespace DedekindZetaZeroFree.KPCplxRotatedKernelEstimates

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable def radialUnit (ρ : ℝ) (u : ℂˣ) : ℂˣ :=
  if hρ : 0 < ρ then
    Units.mk0 ((ρ : ℂ) * (u : ℂ)) (by
      refine mul_ne_zero ?_ u.ne_zero
      exact_mod_cast (ne_of_gt hρ))
  else 1

theorem exists_norm_eq_one_radialUnit_eq (y : ℂˣ) :
    ∃ u : ℂˣ, ‖(u : ℂ)‖ = 1 ∧ radialUnit ‖(y : ℂ)‖ u = y := by
  have hr := norm_pos_iff.mpr y.ne_zero
  let a := Units.mk0 (‖(y : ℂ)‖ : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')
  refine ⟨a⁻¹ * y, ?_, ?_⟩
  · simp only [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
    change (‖(‖(y : ℂ)‖ : ℂ)‖)⁻¹ * ‖(y : ℂ)‖ = 1
    simp
  · apply Units.ext
    simp only [radialUnit, dif_pos hr, Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
    change (‖(y : ℂ)‖ : ℂ) * ((‖(y : ℂ)‖ : ℂ)⁻¹ * (y : ℂ)) = (y : ℂ)
    simp

noncomputable def horizontalRealDerivative (F : ℝ → ℂ → ℂ) : ℝ → ℂ → ℂ :=
  fun ρ x => deriv (fun t : ℝ => F ρ ⟨t, x.im⟩) x.re

instance areaHaar : euclideanArea.IsAddHaarMeasure := by
  unfold euclideanArea
  infer_instance

noncomputable def rationalEnvelope (h : ℕ) (ρ : ℝ) (x : ℂ) : ℝ :=
  ρ ^ (4 / 3 : ℝ) * (ρ ^ 2 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2)

section

variable (h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ)

include hρ in
lemma rationalEnvelope_scaled :
    rationalEnvelope h ρ (ρ • x) =
      ρ ^ (-(4 / 3 : ℝ) - (h : ℝ)) *
        (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2) := by
  unfold rationalEnvelope
  simp [norm_smul, abs_of_pos hρ, mul_pow]
  have he : ρ ^ 2 + ρ ^ 2 * ‖x‖ ^ 2 = ρ ^ 2 * (1 + ‖x‖ ^ 2) := by ring
  rw [he, Real.mul_rpow (sq_nonneg ρ) (by positivity), ← Real.rpow_natCast_mul hρ.le]
  rw [← mul_assoc, ← Real.rpow_add hρ]
  congr 2
  ring

include hρ in
lemma rationalEnvelope_normalized :
    rationalEnvelope h ρ x =
      ρ ^ (-(4 / 3 : ℝ) - (h : ℝ)) *
        (1 + ‖ρ⁻¹ • x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2) := by
  simpa only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] using
    rationalEnvelope_scaled h ρ hρ (ρ⁻¹ • x)

end

lemma rationalEnvelope_one_integrable (h : ℕ) :
    Integrable (fun x : ℂ => (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2))
      euclideanArea := by
  have hh : (Module.finrank ℝ ℂ : ℝ) < (8 / 3 : ℝ) + (h : ℝ) := by
    simp only [Complex.finrank_real_complex, Nat.cast_ofNat]
    linarith
  letI : euclideanArea.IsAddHaarMeasure := by
    infer_instance
  have he : -((8 / 3 : ℝ) + (h : ℝ)) / 2 = -(4 / 3 : ℝ) - (h : ℝ) / 2 := by ring
  simpa only [he] using (integrable_rpow_neg_one_add_norm_sq (μ := euclideanArea) hh)

section

variable (h : ℕ) (ρ : ℝ) (hρ : 0 < ρ)

include hρ in
lemma rationalEnvelope_integrable :
    Integrable (rationalEnvelope h ρ) euclideanArea := by
  exact (((rationalEnvelope_one_integrable h).comp_smul (inv_ne_zero hρ.ne')).const_mul (ρ ^ (-(4 / 3 : ℝ) - (h : ℝ)))).congr (Filter.Eventually.of_forall fun x => (rationalEnvelope_normalized h ρ hρ x).symm)

include hρ in
lemma rationalEnvelope_integral :
    (∫ x : ℂ, rationalEnvelope h ρ x ∂euclideanArea) =
      (∫ x : ℂ, (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2) ∂euclideanArea) *
        ρ ^ ((2 / 3 : ℝ) - (h : ℝ)) := by
  simp_rw [rationalEnvelope_normalized h ρ hρ]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg euclideanArea
    (fun x : ℂ => (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2)) hρ.le]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hρ]
  ring_nf

end

lemma integral_bound_of_rationalEnvelope (h : ℕ) (ρ C : ℝ) (hρ : 0 < ρ)
    (F : ℂ → ℂ) (hm : AEStronglyMeasurable F euclideanArea)
    (hb : ∀ x, ‖F x‖ ≤ C * rationalEnvelope h ρ x) :
    Integrable (fun x => ‖F x‖) euclideanArea ∧
      (∫ x, ‖F x‖ ∂euclideanArea) ≤
        C * (∫ x : ℂ, (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2) ∂euclideanArea) *
          ρ ^ ((2 / 3 : ℝ) - (h : ℝ)) := by
  have hi := (rationalEnvelope_integrable h ρ hρ).const_mul C
  have hf := hi.mono' hm (Filter.Eventually.of_forall hb)
  refine ⟨hf.norm, ?_⟩
  calc
    _ ≤ ∫ x, C * rationalEnvelope h ρ x ∂euclideanArea :=
      integral_mono hf.norm hi hb
    _ = _ := by rw [integral_const_mul, rationalEnvelope_integral h ρ hρ]; ring

alias bottomRowNormSq_pos := DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts.bottom_pos

end DedekindZetaZeroFree.KPCplxRotatedKernelEstimates

end
