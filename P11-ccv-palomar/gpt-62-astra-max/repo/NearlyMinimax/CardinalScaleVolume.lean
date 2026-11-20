module

public import NearlyMinimax.CardinalScaleTail


@[expose] public section

/-! Actual volume of the compact logarithmic scale cutoff. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def finiteOrthantCutoff {q : ℕ} (A : ℝ) (s : Fin q → ℝ) : ℝ :=
  if ∑ j, s j ≤ A then Real.exp (∑ j, s j) else 0

section
variable {ι κ : Type*} {m : ℕ} {A : ℝ}

def orthantSumCutoff [Fintype ι] (A : ℝ) (z : ℝ × (ι → ℝ)) : ℝ :=
  if z.1 + ∑ j, z.2 j ≤ A then Real.exp (z.1 + ∑ j, z.2 j) else 0

theorem finite_orthant_cutoff_integrable {q : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    Integrable (finiteOrthantCutoff A : (Fin q → ℝ) → ℝ) (exponentialOrthantMeasure (Fin q)) := by
  have hm : Measurable (finiteOrthantCutoff A : (Fin q → ℝ) → ℝ) := by
    exact Measurable.ite (measurableSet_le (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) measurable_const)
      (Real.measurable_exp.comp (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)) measurable_const
  apply (orthant_cube_indicator_integrable A (Real.exp A)).mono' hm.aestronglyMeasurable
  rw [exponential_orthant_measure_eq_restrict]
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  unfold finiteOrthantCutoff
  by_cases hsum : ∑ j, s j ≤ A
  · rw [ite_eq_left hsum, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    have hcube : s ∈ Icc 0 (fun _ => A) := by
      refine ⟨hs, ?_⟩
      intro j
      exact (Finset.single_le_sum (fun l _ => hs l) (Finset.mem_univ j)).trans hsum
    rw [Set.indicator_of_mem hcube]
    exact Real.exp_le_exp.mpr hsum
  · rw [ite_eq_right hsum, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _

theorem orthant_cutoff_split_integral (A : ℝ) :
    (∫ s : Fin (m + 1) → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin (m + 1))) =
      ∫ z : ℝ × (Fin m → ℝ), orthantSumCutoff A z
      ∂((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))) :=
  (orthant_sum_split (fun t => if t ≤ A then Real.exp t else 0)).2

theorem orthant_cutoff_pair_integrable (hA : 0 ≤ A) :
    Integrable (orthantSumCutoff A : (ℝ × (Fin m → ℝ)) → ℝ)
      ((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))) :=
  (orthant_sum_split (fun t => if t ≤ A then Real.exp t else 0)).1.mpr (finite_orthant_cutoff_integrable hA)

theorem orthant_cutoff_scalar_integral (A S : ℝ) :
    (∫ v : ℝ in Ici 0, if v + S ≤ A then Real.exp (v + S) else 0) =
      if S ≤ A then Real.exp A - Real.exp S else 0 := by
  have he : (fun v : ℝ => if v + S ≤ A then Real.exp (v + S) else 0) =
      (Iic (A - S)).indicator (fun v : ℝ => Real.exp (v + S)) := by
    funext v
    have hh : v + S ≤ A ↔ v ≤ A - S := by constructor <;> intro h <;> linarith
    simp only [Set.indicator, mem_Iic, hh]
  rw [he, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic (A - S) ∩ Ici (0 : ℝ) = Icc 0 (A - S) := by grind
  rw [hs]
  by_cases h : S ≤ A
  · rw [ite_eq_left h]
    have hn : 0 ≤ A - S := by linarith
    have hf : (fun v : ℝ => Real.exp (v + S)) = fun v => Real.exp S * Real.exp v := by
      funext v
      rw [Real.exp_add]
      ring
    rw [hf, integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hn, integral_exp]
    rw [Real.exp_zero, mul_sub, ← Real.exp_add, mul_one]
    simp
  · aesop

/-- Correct log-degree volume estimate: integrating the distinguished
coordinate eliminates one power of the simplex radius. -/
theorem finite_orthant_cutoff_integral_le (hA : 0 ≤ A) :
    (∫ s : Fin (m + 1) → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin (m + 1))) ≤
      Real.exp A * A ^ m := by
  rw [orthant_cutoff_split_integral, integral_prod_symm _ (orthant_cutoff_pair_integrable hA)]
  have hdom : (fun s : Fin m → ℝ => ∫ v : ℝ in Ici 0, orthantSumCutoff A (v, s)) ≤ᵐ[
      exponentialOrthantMeasure (Fin m)]
      (Icc 0 (fun _ => A)).indicator (fun _ => Real.exp A) := by
    rw [exponential_orthant_measure_eq_restrict]
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    change (∫ v : ℝ in Ici 0, if v + ∑ j, s j ≤ A then Real.exp (v + ∑ j, s j) else 0) ≤ _
    rw [orthant_cutoff_scalar_integral]
    by_cases hcube : s ∈ Icc 0 (fun _ => A)
    · rw [Set.indicator_of_mem hcube]
      split_ifs
      · linarith [Real.exp_nonneg (∑ j, s j)]
      · positivity
    · have hsum : ¬ ∑ j, s j ≤ A := by
        intro hsum
        apply hcube
        refine ⟨hs, ?_⟩
        intro j
        exact (Finset.single_le_sum (fun l _ => hs l) (Finset.mem_univ j)).trans hsum
      rw [ite_eq_right hsum, Set.indicator_of_notMem hcube]
  have h := integral_mono_ae (orthant_cutoff_pair_integrable hA).integral_prod_right
    (orthant_cube_indicator_integrable A (Real.exp A)) hdom
  rw [orthant_cube_indicator_integral hA] at h
  simpa only [Fintype.card_fin, mul_comm] using h

def logScaleCutoff [Fintype ι] (A : ℝ) (t : ι → ℝ) : ℝ :=
  if ∑ j, Real.log (1 + t j) ≤ A then 1 else 0

theorem log_scale_cutoff_change_pointwise [Fintype ι] (A : ℝ) (s : ι → ℝ) :
    (∏ j, Real.exp (s j)) * logScaleCutoff A (exponentialScaleMap s) =
      if ∑ j, s j ≤ A then Real.exp (∑ j, s j) else 0 := by
  classical
  have he : ∀ j : ι, 1 + exponentialScaleMap s j = Real.exp (s j) := by
    intro j
    unfold exponentialScaleMap
    ring
  unfold logScaleCutoff
  simp_rw [he, Real.log_exp]
  split_ifs
  · rw [mul_one, ← Real.exp_sum]
  · exact mul_zero _

theorem finite_log_scale_cutoff_integral {q : ℕ} (A : ℝ) :
    (∫ t : Fin q → ℝ in Ici 0, logScaleCutoff A t) =
      ∫ s : Fin q → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin q) := by
  rw [integral_exponential_scale_change, exponential_orthant_measure_eq_restrict]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => log_scale_cutoff_change_pointwise A s

theorem log_scale_cutoff_integral_reindex [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (A : ℝ) :
    (∫ t : ι → ℝ in Ici 0, logScaleCutoff A t) =
      ∫ s : κ → ℝ in Ici 0, logScaleCutoff A s := by
  classical
  rw [← exponential_orthant_measure_eq_restrict, ← exponential_orthant_measure_eq_restrict]
  unfold exponentialOrthantMeasure
  have hp := measurePreserving_piCongrLeft (fun _ : ι => volume.restrict (Ici (0 : ℝ))) e
  rw [← hp.integral_comp']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    have hs := e.sum_comp (fun j : ι => Real.log (1 + ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s) j))
    simp [MeasurableEquiv.piCongrLeft_apply_apply] at hs
    unfold logScaleCutoff
    dsimp
    rw [← hs]

end

variable {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (T : ℝ)

theorem spatial_scale_domain_original :
    spatialScaleDomain i T = Ici 0 ∩
      {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T} := by
  ext t
  have he (ht : t ∈ Ici 0) :
      spatialScaleLogSum t = ∑ j, Real.log (1 + t j) := by
    apply Finset.sum_congr rfl
    intro j _
    have htj : (0 : ℝ) ≤ t j := ht j
    rw [max_eq_right htj]
  constructor
  · rintro ⟨ht, hlog⟩
    refine ⟨ht, ?_⟩
    change _ ≤ _ at hlog
    rw [he ht] at hlog
    exact hlog
  · rintro ⟨ht, hlog⟩
    refine ⟨ht, ?_⟩
    change _ ≤ _
    rw [he ht]
    exact hlog

theorem spatial_scale_domain_volume_eq_cutoff :
    (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) =
      ∫ t : SpatialScaleVector i in Ici 0, logScaleCutoff (2 * Real.log T) t := by
  have hlog : Measurable (fun t : SpatialScaleVector i => ∑ j, Real.log (1 + t j)) :=
    by fun_prop
  have hm : MeasurableSet {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T} :=
    measurableSet_le hlog measurable_const
  have he : (logScaleCutoff (2 * Real.log T) : SpatialScaleVector i → ℝ) =
      {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T}.indicator (fun _ => 1) := by
    rfl
  rw [he, integral_indicator hm, Measure.restrict_restrict hm]
  have hs : {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T} ∩ Ici 0 =
      spatialScaleDomain i T := by rw [spatial_scale_domain_original, Set.inter_comm]
  rw [hs, integral_const]
  simp

include hn in
/-- Genuine Lebesgue volume of the original logarithmic scale simplex. -/
theorem spatial_scale_domain_volume_le {T : ℝ} (hT : 1 ≤ T) :
    (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) ≤
      T ^ 2 * (2 * Real.log T) ^ (n - 2) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by
    rw [spatial_scale_index_card]
    omega
  rw [spatial_scale_domain_volume_eq_cutoff]
  have h := (by rw [log_scale_cutoff_integral_reindex (Fintype.equivFinOfCardEq hcard).symm, finite_log_scale_cutoff_integral]; exact finite_orthant_cutoff_integral_le (by linarith [Real.log_nonneg hT] : 0 ≤ 2 * Real.log T) : ∫ (t : SpatialScaleIndex i → ℝ) in Ici 0, logScaleCutoff (2 * Real.log T) t ≤ Real.exp (2 * Real.log T) * (2 * Real.log T) ^ (n - 2))
  have he : Real.exp (2 * Real.log T) = T ^ 2 := by
    have hTpos : 0 < T := by positivity
    simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using Real.exp_nat_mul (Real.log T) 2
  rw [he] at h
  exact h

include hn in
theorem spatial_scale_domain_volume_le_uniform
    {T : ℝ} (hT : 1 ≤ T) :
    (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) ≤
      2 ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  have hlog  := Real.log_nonneg hT
  have h := pow_le_pow_left₀ hlog (by linarith : Real.log T ≤ 1 + Real.log T) (n - 2)
  have ht := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n - 2 ≤ n - 1)
  have hh := mul_le_mul h ht (by positivity : 0 ≤ (2 : ℝ) ^ (n - 2))
    (by positivity : 0 ≤ (1 + Real.log T) ^ (n - 2))
  have hhh := mul_le_mul_of_nonneg_right hh (sq_nonneg T)
  calc
    _ ≤ _ := spatial_scale_domain_volume_le hn i hT
    _ ≤ _ := by rw [mul_pow]; nlinarith [hhh]

end NearlyMinimax
