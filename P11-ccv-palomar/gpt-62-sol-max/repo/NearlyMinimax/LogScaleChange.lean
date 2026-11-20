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

def exponentialScaleMap (s : ι → ℝ) : ι → ℝ := fun j => Real.exp (s j) - 1

@[simp] theorem one_add_exponentialScaleMap (s : ι → ℝ) (j : ι) :
    1 + exponentialScaleMap s j = Real.exp (s j) := by
  unfold exponentialScaleMap
  ring

/-- Relabeling the orthant coordinates preserves product Lebesgue measure. -/
theorem orthant_reindex_preserving {κ : Type*} [Fintype κ] (e : κ ≃ ι) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e)
      (volume.restrict (Ici (0 : κ → ℝ))) (volume.restrict (Ici (0 : ι → ℝ))) := by
  rw [← exponential_orthant_measure_eq_restrict, ← exponential_orthant_measure_eq_restrict]
  exact measurePreserving_piCongrLeft (fun _ : ι => volume.restrict (Ici (0 : ℝ))) e

theorem orthant_reindex_sum {κ : Type*} [Fintype κ] (e : κ ≃ ι) (s : κ → ℝ) (f : ℝ → ℝ) :
    (∑ j, f (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e s j)) = ∑ j, f (s j) := by
  simpa only [MeasurableEquiv.piCongrLeft_apply_apply] using
    (e.sum_comp fun j => f (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e s j)).symm

def exponentialScaleDerivative (s : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun j => Real.exp (s j) • ContinuousLinearMap.proj j)

section
variable (s : ι → ℝ)

theorem exponential_scale_hasFDerivAt :
    HasFDerivAt exponentialScaleMap (exponentialScaleDerivative s) s := by
  apply hasFDerivAt_pi.mpr
  intro j
  have h : HasFDerivAt (fun x : ι → ℝ => Real.exp (x j))
      (Real.exp (s j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j)) s := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (s j)).comp_hasFDerivAt s (hasFDerivAt_apply j s)
  exact h.sub_const 1

theorem exponential_scale_derivative_det :
    (exponentialScaleDerivative s).det = ∏ j, Real.exp (s j) := by
  have he : (exponentialScaleDerivative s).toLinearMap =
      LinearMap.pi (fun j => ((Real.exp (s j)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp (LinearMap.proj j)) := by
    rfl
  change (exponentialScaleDerivative s).toLinearMap.det = _
  rw [he, LinearMap.det_pi]
  simp only [LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one]

end

theorem exponential_scale_injective : Function.Injective (exponentialScaleMap : (ι → ℝ) → (ι → ℝ)) := by
  intro s t h
  funext j
  simpa [exponentialScaleMap] using congrFun h j

theorem exponential_scale_image_orthant :
    exponentialScaleMap '' Ici (0 : ι → ℝ) = Ici (0 : ι → ℝ) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    intro j
    have hsj : (0 : ℝ) ≤ s j := hs j
    change 0 ≤ Real.exp (s j) - 1
    simp_all
  · intro ht
    refine ⟨fun j => Real.log (1 + t j), ?_, ?_⟩
    · intro j
      have htj : (0 : ℝ) ≤ t j := ht j
      apply Real.log_nonneg <;> simp_all
    · funext j
      have htj : (0 : ℝ) ≤ t j := ht j
      change Real.exp (Real.log (1 + t j)) - 1 = t j
      rw [Real.exp_log (by linarith)]
      ring

/-- The same Jacobian gives both change of variables and the integrability equivalence. -/
theorem exponential_scale_change (f : (ι → ℝ) → ℝ) :
    ((∫ t in Ici 0, f t) =
      ∫ s in Ici 0, (∏ j, Real.exp (s j)) * f (exponentialScaleMap s)) ∧
    (IntegrableOn f (Ici 0) ↔
      IntegrableOn (fun s => (∏ j, Real.exp (s j)) * f (exponentialScaleMap s)) (Ici 0)) := by
  have hd (s : ι → ℝ) (_ : s ∈ Ici 0) := (exponential_scale_hasFDerivAt s).hasFDerivWithinAt (s := Ici 0)
  have hi := exponential_scale_injective (ι := ι) |>.injOn (s := Ici 0)
  have hdet (s : ι → ℝ) : |(exponentialScaleDerivative s).det| = ∏ j, Real.exp (s j) := by
    rw [exponential_scale_derivative_det, abs_of_nonneg (Finset.prod_nonneg fun _ _ => Real.exp_nonneg _)]
  constructor
  · simpa only [exponential_scale_image_orthant, hdet, smul_eq_mul] using
      integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_Ici hd hi f
  · simpa only [exponential_scale_image_orthant, hdet, smul_eq_mul] using
      integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_Ici hd hi f

/-- The closed logarithmic scale tail with its actual power-law integrand. -/
def logScaleTail (b A : ℝ) (t : ι → ℝ) : ℝ :=
  if A ≤ ∑ j, Real.log (1 + t j) then ∏ j, (1 + t j) ^ (-b - 1 : ℝ) else 0

theorem log_scale_tail_change_pointwise (b A : ℝ) (s : ι → ℝ) :
    (∏ j, Real.exp (s j)) * logScaleTail b A (exponentialScaleMap s) =
      if A ≤ ∑ j, s j then Real.exp (-(b * ∑ j, s j)) else 0 := by
  simp only [logScaleTail, one_add_exponentialScaleMap, Real.log_exp]
  split_ifs
  · rw [← Finset.prod_mul_distrib]
    have hp : ∀ j : ι, Real.exp (s j) * Real.exp (s j) ^ (-b - 1 : ℝ) =
        Real.exp (-(b * s j)) := by
      intro j
      simp [← Real.exp_mul, ← Real.exp_add] <;> ring
    simp_rw [hp]
    simp [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  simp

theorem finite_log_scale_tail_integral {q : ℕ} (b A : ℝ) :
    (∫ t : Fin q → ℝ in Ici 0, logScaleTail b A t) =
      ∫ s : Fin q → ℝ, finiteOrthantTail b A s ∂exponentialOrthantMeasure (Fin q) := by
  rw [(exponential_scale_change _).1, exponential_orthant_measure_eq_restrict]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => log_scale_tail_change_pointwise b A s

section
variable {m : ℕ}

theorem finite_log_scale_tail_integrable {b : ℝ} (hb : 0 < b) (A : ℝ) :
    IntegrableOn (logScaleTail b A : (Fin (m + 1) → ℝ) → ℝ) (Ici 0) := by
  apply (exponential_scale_change _).2.mpr
  have h := finite_orthant_tail_integrable (m := m) hb A
  rw [exponential_orthant_measure_eq_restrict] at h
  have he : (fun s : Fin (m + 1) → ℝ => (∏ j, Real.exp (s j)) *
      logScaleTail b A (exponentialScaleMap s)) = finiteOrthantTail b A := by
    funext s
    exact log_scale_tail_change_pointwise b A s
  rw [he]
  assumption

/-- Quantitative logarithmic-simplex tail with the actual scale Jacobian. -/
theorem finite_log_scale_tail_integral_uniform {b A : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ t : Fin (m + 1) → ℝ in Ici 0, logScaleTail b A t) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  rw [finite_log_scale_tail_integral]
  exact finite_orthant_tail_integral_uniform hb hA

end

end NearlyMinimax
