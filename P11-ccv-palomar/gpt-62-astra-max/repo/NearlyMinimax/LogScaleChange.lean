module

public import NearlyMinimax.ExponentialOrthantTail


@[expose] public section

/-! Actual multivariable logarithmic change of variables for the cardinal
scale integrals. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section
variable (s : ι → ℝ)

def exponentialScaleMap : ι → ℝ := fun j => Real.exp (s j) - 1

def exponentialScaleDerivative : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun j => Real.exp (s j) • ContinuousLinearMap.proj j)

theorem exponential_scale_hasFDerivAt :
    HasFDerivAt exponentialScaleMap (exponentialScaleDerivative s) s := by
  apply hasFDerivAt_pi.mpr
  intro j
  have h : HasFDerivAt (fun x => Real.exp (x j))
      (Real.exp (s j) • (ContinuousLinearMap.proj (R := ℝ) j)) s := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (s j)).comp_hasFDerivAt s (hasFDerivAt_apply j s)
  exact h.sub_const 1

theorem exponential_scale_derivative_det :
    (exponentialScaleDerivative s).det = ∏ j, Real.exp (s j) := by
  have he : (exponentialScaleDerivative s).toLinearMap =
      LinearMap.pi (fun j => ((Real.exp (s j)) • LinearMap.id).comp (LinearMap.proj j)) := rfl
  change (exponentialScaleDerivative s).toLinearMap.det = _
  rw [he, LinearMap.det_pi]
  simp

end

theorem exponential_scale_injective : Function.Injective (exponentialScaleMap : (ι → ℝ) → (ι → ℝ)) := by
  intro s t h
  funext j
  apply Real.exp_injective
  have hj := congrFun h j
  change Real.exp (s j) - 1 = Real.exp (t j) - 1 at hj
  linarith

theorem exponential_scale_image_orthant :
    exponentialScaleMap '' Ici 0 = Ici (0 : ι → ℝ) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    intro j
    change 0 ≤ Real.exp (s j) - 1
    linarith [Real.one_le_exp_iff.mpr (hs j)]
  · intro ht
    refine ⟨fun j => Real.log (1 + t j), ?_, ?_⟩
    · intro j
      have htj : 0 ≤ t j := ht j
      exact Real.log_nonneg (by linarith)
    · funext j
      have htj : 0 ≤ t j := ht j
      change _ - 1 = _
      rw [Real.exp_log (by linarith)]
      ring

section
variable (f : (ι → ℝ) → ℝ) {q : ℕ} (b A : ℝ)

/-- Change of variables for every actual Bochner integrand, over the entire
positive orthant. -/
theorem integral_exponential_scale_change :
    (∫ t in Ici 0, f t) =
      ∫ s in Ici 0, (∏ j, Real.exp (s j)) * f (exponentialScaleMap s) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    (s := Ici 0) measurableSet_Ici
    (fun s _ => (exponential_scale_hasFDerivAt s).hasFDerivWithinAt)
    exponential_scale_injective.injOn f
  rw [exponential_scale_image_orthant] at h
  have hdet : ∀ s : ι → ℝ, |(exponentialScaleDerivative s).det| = ∏ j, Real.exp (s j) := by
    intro s
    rw [exponential_scale_derivative_det, abs_of_nonneg (by positivity)]
  simp_all

theorem integrableOn_exponential_scale_change_iff :
    IntegrableOn f (Ici 0) ↔
      IntegrableOn (fun s => (∏ j, Real.exp (s j)) * f (exponentialScaleMap s)) (Ici 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (s := Ici 0) measurableSet_Ici
    (fun s _ => (exponential_scale_hasFDerivAt s).hasFDerivWithinAt)
    exponential_scale_injective.injOn f
  rw [exponential_scale_image_orthant] at h
  have hdet : ∀ s : ι → ℝ, |(exponentialScaleDerivative s).det| = ∏ j, Real.exp (s j) := by
    intro s
    rw [exponential_scale_derivative_det, abs_of_nonneg (by positivity)]
  simp_all

/-- The closed logarithmic scale tail with its actual power-law integrand. -/
def logScaleTail (t : ι → ℝ) : ℝ :=
  if A ≤ ∑ j, Real.log (1 + t j) then ∏ j, (1 + t j) ^ (-b - 1) else 0

theorem log_scale_tail_change_pointwise (s : ι → ℝ) :
    (∏ j, Real.exp (s j)) * logScaleTail b A (exponentialScaleMap s) =
      if A ≤ ∑ j, s j then Real.exp (-(b * ∑ j, s j)) else 0 := by
  have he : ∀ j, 1 + exponentialScaleMap s j = Real.exp (s j) := by
    intro j
    unfold exponentialScaleMap
    ring
  unfold logScaleTail
  simp_rw [he, Real.log_exp]
  split_ifs
  · rw [← Finset.prod_mul_distrib]
    have hp : ∀ j, Real.exp (s j) * Real.exp (s j) ^ (-b - 1) =
        Real.exp (-(b * s j)) := by
      intro j
      rw [← Real.exp_mul, ← Real.exp_add]
      ring
    simp_rw [hp]
    rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  · exact mul_zero _

theorem finite_log_scale_tail_integral :
    (∫ t : Fin q → ℝ in Ici 0, logScaleTail b A t) =
      ∫ s, finiteOrthantTail b A s ∂exponentialOrthantMeasure (Fin q) := by
  rw [integral_exponential_scale_change, exponential_orthant_measure_eq_restrict]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => log_scale_tail_change_pointwise ..

end

variable {m : ℕ} {b : ℝ}

theorem finite_log_scale_tail_integrable (hb : 0 < b) (A : ℝ) :
    IntegrableOn (logScaleTail b A : (Fin (m + 1) → ℝ) → ℝ) (Ici 0) := by
  apply (integrableOn_exponential_scale_change_iff _).mpr
  have h := finite_orthant_tail_integrable (m := m) hb A
  rw [exponential_orthant_measure_eq_restrict] at h
  have he : (fun s : Fin (m + 1) → ℝ => (∏ j, Real.exp (s j)) *
      logScaleTail b A (exponentialScaleMap s)) = finiteOrthantTail b A := by
    funext s
    exact log_scale_tail_change_pointwise ..
  rw [he]
  exact h

/-- Quantitative logarithmic-simplex tail with the actual scale Jacobian. -/
theorem finite_log_scale_tail_integral_uniform {A : ℝ}
    (hb : (1 / 2) ≤ b) (hA : 0 ≤ A) :
    (∫ t : Fin (m + 1) → ℝ in Ici 0, logScaleTail b A t) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  rw [finite_log_scale_tail_integral]
  exact by rw [finite_orthant_tail_split_integral]; simpa using orthant_sum_tail_integral_uniform (ι := Fin _) hb hA

end NearlyMinimax
