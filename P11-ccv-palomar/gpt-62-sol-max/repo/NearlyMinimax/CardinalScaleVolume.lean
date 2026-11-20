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

def orthantSumCutoff {ι : Type*} [Fintype ι] (A : ℝ) (z : ℝ × (ι → ℝ)) : ℝ :=
  if z.1 + ∑ j, z.2 j ≤ A then Real.exp (z.1 + ∑ j, z.2 j) else 0

private theorem orthant_mem_cube {ι : Type*} [Fintype ι] {s : ι → ℝ} {A : ℝ}
    (hs : s ∈ Ici 0) (hA : ∑ j, s j ≤ A) : s ∈ Icc 0 (fun _ => A) :=
  ⟨hs, fun j => (Finset.single_le_sum (fun l _ => hs l) (Finset.mem_univ j)).trans hA⟩

theorem finite_orthant_cutoff_integrable {q : ℕ} {A : ℝ} :
    Integrable (finiteOrthantCutoff A : (Fin q → ℝ) → ℝ) (exponentialOrthantMeasure (Fin q)) := by
  have hm : Measurable (finiteOrthantCutoff A : (Fin q → ℝ) → ℝ) := by
    exact Measurable.ite (measurableSet_le (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) measurable_const)
          (Real.measurable_exp.comp (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)) measurable_const
  apply (orthant_cube_indicator_integrable A (Real.exp A)).mono' hm.aestronglyMeasurable
  rw [exponential_orthant_measure_eq_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : Fin q → ℝ)))] with s hs
  unfold finiteOrthantCutoff
  by_cases hsum : ∑ j, s j ≤ A
  · rw [ite_eq_left hsum, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    rw [Set.indicator_of_mem (orthant_mem_cube hs hsum), Real.exp_le_exp]
    exact hsum
  · rw [ite_eq_right hsum, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _

theorem orthant_cutoff_pair_integrable {m : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    Integrable (orthantSumCutoff A : (ℝ × (Fin m → ℝ)) → ℝ)
      ((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))) :=
  (orthant_sum_split_integrable (fun t => if t ≤ A then Real.exp t else 0)).1
    (finite_orthant_cutoff_integrable)

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
      grind [Real.exp_add]
    simp [hf, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hn, integral_exp, ← Real.exp_add, show S + (A - S) = A by ring]
  simp_all

/-- Correct log-degree volume estimate: integrating the distinguished
coordinate eliminates one power of the simplex radius. -/
theorem finite_orthant_cutoff_integral_le {m : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    (∫ s : Fin (m + 1) → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin (m + 1))) ≤
      Real.exp A * A ^ m := by
  have h := orthant_sum_split_integral (m := m) (fun t => if t ≤ A then Real.exp t else 0)
  change (∫ s : Fin (m + 1) → ℝ, finiteOrthantCutoff A s ∂_) = ∫ z, orthantSumCutoff A z ∂_ at h
  rw [h, integral_prod_symm _ (orthant_cutoff_pair_integrable hA)]
  have hdom : (fun s : Fin m → ℝ => ∫ v : ℝ in Ici 0, orthantSumCutoff A (v, s)) ≤ᵐ[
      exponentialOrthantMeasure (Fin m)]
      (Icc (0 : Fin m → ℝ) (fun _ => A)).indicator (fun _ => Real.exp A) := by
    rw [exponential_orthant_measure_eq_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : Fin m → ℝ)))] with s hs
    change (∫ v : ℝ in Ici 0, if v + ∑ j, s j ≤ A then Real.exp (v + ∑ j, s j) else 0) ≤ _
    rw [orthant_cutoff_scalar_integral]
    by_cases hcube : s ∈ Icc (0 : Fin m → ℝ) (fun _ => A)
    · rw [Set.indicator_of_mem hcube]
      split_ifs
      · linarith [Real.exp_nonneg (∑ j, s j)]
      positivity
    · rw [ite_eq_right (fun h => hcube (orthant_mem_cube hs h)), Set.indicator_of_notMem hcube]
  have h := integral_mono_ae (orthant_cutoff_pair_integrable hA).integral_prod_right
    (orthant_cube_indicator_integrable A (Real.exp A)) hdom
  rw [orthant_cube_indicator_integral hA] at h
  simpa only [Fintype.card_fin, mul_comm] using h

def logScaleCutoff {ι : Type*} [Fintype ι] (A : ℝ) (t : ι → ℝ) : ℝ :=
  if ∑ j, Real.log (1 + t j) ≤ A then 1 else 0

theorem log_scale_cutoff_change_pointwise {ι : Type*} [Fintype ι] (A : ℝ) (s : ι → ℝ) :
    (∏ j, Real.exp (s j)) * logScaleCutoff A (exponentialScaleMap s) =
      if ∑ j, s j ≤ A then Real.exp (∑ j, s j) else 0 := by
  classical
  simp only [logScaleCutoff, one_add_exponentialScaleMap, Real.log_exp, mul_ite, mul_one, mul_zero, Real.exp_sum]

theorem finite_log_scale_cutoff_integral {q : ℕ} (A : ℝ) :
    (∫ t : Fin q → ℝ in Ici 0, logScaleCutoff A t) =
      ∫ s : Fin q → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin q) := by
  rw [(exponential_scale_change _).1, exponential_orthant_measure_eq_restrict]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => log_scale_cutoff_change_pointwise A s

theorem log_scale_cutoff_integral_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (A : ℝ) :
    (∫ t : ι → ℝ in Ici 0, logScaleCutoff A t) =
      ∫ s : κ → ℝ in Ici 0, logScaleCutoff A s := by
  classical
  rw [← (orthant_reindex_preserving e).integral_comp']
  exact integral_congr_ae (Filter.Eventually.of_forall fun s => by
    simp only [logScaleCutoff, orthant_reindex_sum e s (fun x => Real.log (1 + x))])

theorem log_scale_cutoff_integral_le_of_card {ι : Type*} [Fintype ι]
    {m : ℕ} (hcard : Fintype.card ι = m + 1) {A : ℝ} (hA : 0 ≤ A) :
    (∫ t : ι → ℝ in Ici 0, logScaleCutoff A t) ≤ Real.exp A * A ^ m := by
  rw [log_scale_cutoff_integral_reindex (Fintype.equivFinOfCardEq hcard).symm,
    finite_log_scale_cutoff_integral]
  exact finite_orthant_cutoff_integral_le hA

section
variable {n : ℕ}


theorem spatial_scale_domain_volume_eq_cutoff (i : Fin n) (T : ℝ) :
    (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) =
      ∫ t : SpatialScaleVector i in Ici 0, logScaleCutoff (2 * Real.log T) t := by
  have hlog : Measurable (fun t : SpatialScaleVector i => ∑ j, Real.log (1 + t j)) :=
    Finset.measurable_sum _ fun j _ => Real.measurable_log.comp
      (measurable_const.add (measurable_pi_apply j))
  have hm : MeasurableSet {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T} :=
    measurableSet_le hlog measurable_const
  have he : (logScaleCutoff (2 * Real.log T) : SpatialScaleVector i → ℝ) =
      {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T}.indicator (fun _ => 1) := by
    rfl
  rw [he, integral_indicator hm, Measure.restrict_restrict hm]
  have hs : {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T} ∩ Ici 0 =
      spatialScaleDomain i T := by rw [spatial_scale_domain_original, Set.inter_comm]
  norm_num [hs, integral_const]

/-- Genuine Lebesgue volume of the original logarithmic scale simplex. -/
theorem spatial_scale_domain_volume_le (hn : 2 ≤ n) (i : Fin n) {T : ℝ} (hT : 1 ≤ T) :
    (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) ≤
      T ^ 2 * (2 * Real.log T) ^ (n - 2) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by
    rw [spatial_scale_index_card]
    omega
  rw [spatial_scale_domain_volume_eq_cutoff]
  have h := log_scale_cutoff_integral_le_of_card hcard
    (by linarith [Real.log_nonneg hT] : 0 ≤ 2 * Real.log T)
  have he : Real.exp (2 * Real.log T) = T ^ 2 := by
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
    simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using Real.exp_nat_mul (Real.log T) 2
  simpa only [he] using h

theorem spatial_scale_domain_volume_le_uniform (hn : 2 ≤ n) (i : Fin n)
    {T : ℝ} (hT : 1 ≤ T) :
    (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) ≤
      2 ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  have hlog := Real.log_nonneg hT
  have h := pow_le_pow_left₀ hlog (by linarith : Real.log T ≤ 1 + Real.log T) (n - 2)
  have ht := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n - 2 ≤ n - 1)
  have hh := mul_le_mul h ht (by positivity : 0 ≤ (2 : ℝ) ^ (n - 2))
    (by positivity : 0 ≤ (1 + Real.log T) ^ (n - 2))
  have hhh := mul_le_mul_of_nonneg_right hh (sq_nonneg T)
  calc
    _ ≤ _ := spatial_scale_domain_volume_le hn i hT
    _ ≤ _ := by rw [mul_pow]; linarith

end

end NearlyMinimax
