module

public import NearlyMinimax.LogScaleChange


@[expose] public section

/-! Actual logarithmic scale-domain complement bound for the integrated
cardinal interpolation matrix. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

section
variable (e : κ ≃ ι) (b A : ℝ)
include e

theorem log_scale_tail_reindex (s : κ → ℝ) :
    logScaleTail b A ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) s) = logScaleTail b A s := by
  have hs := e.sum_comp (fun j => Real.log (1 + ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) s) j))
  have hp := e.prod_comp (fun j => (1 + ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) s) j) ^ (-b - 1))
  simp [MeasurableEquiv.piCongrLeft_apply_apply] at hs hp
  simp_all [logScaleTail]

theorem log_scale_tail_integral_reindex :
    (∫ t : ι → ℝ in Ici 0, logScaleTail b A t) =
      ∫ s : κ → ℝ in Ici 0, logScaleTail b A s := by
  rw [← exponential_orthant_measure_eq_restrict, ← exponential_orthant_measure_eq_restrict]
  unfold exponentialOrthantMeasure
  rw [← (measurePreserving_piCongrLeft (fun _ => volume.restrict (Ici 0)) e).integral_comp']
  simp_rw [log_scale_tail_reindex]

end

section
variable {m : ℕ} (hcard : Fintype.card ι = m + 1) {b : ℝ} (hb : 0 < b) (A : ℝ)

include hcard hb in
theorem log_scale_tail_integrable_of_card :
    IntegrableOn (logScaleTail b A : (ι → ℝ) → ℝ) (Ici 0) := by
  let e  := (Fintype.equivFinOfCardEq hcard).symm
  rw [IntegrableOn, ← exponential_orthant_measure_eq_restrict]
  apply ((measurePreserving_piCongrLeft (fun _ => volume.restrict (Ici 0)) e).integrable_comp_emb (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e).measurableEmbedding).mp
  have he : (logScaleTail b A) ∘ (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) =
      (logScaleTail b A) := by
    funext s
    exact log_scale_tail_reindex e b A s
  rw [he]
  have h := finite_log_scale_tail_integrable (m := m) hb A
  rw [IntegrableOn, ← exponential_orthant_measure_eq_restrict] at h
  exact h

def strictLogScaleTail (b A : ℝ) (t : ι → ℝ) : ℝ :=
  ({t | A < ∑ j, Real.log (1 + t j)}).indicator (logScaleTail b A) t

include hcard hb in
theorem strict_log_scale_tail_integrable_of_card :
    IntegrableOn (strictLogScaleTail b A : (ι → ℝ) → ℝ) (Ici 0) := (log_scale_tail_integrable_of_card hcard hb A).indicator
    (measurableSet_lt measurable_const (by fun_prop))

include hcard in
theorem strict_log_scale_tail_integral_le {A : ℝ} (hb : (1 / 2) ≤ b) (hA : 0 ≤ A) :
    (∫ t : ι → ℝ in Ici 0, strictLogScaleTail b A t) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  have hbpos : 0 < b := by positivity
  have hnonneg : ∀ᵐ t : ι → ℝ ∂volume.restrict (Ici 0), 0 ≤ logScaleTail b A t := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    unfold logScaleTail
    split_ifs
    · apply Finset.prod_nonneg
      bound
    · positivity
  calc
    _ ≤ _ :=
      integral_mono_ae (strict_log_scale_tail_integrable_of_card hcard hbpos A)
        (log_scale_tail_integrable_of_card hcard hbpos A) (by
          filter_upwards [hnonneg] with t ht
          unfold strictLogScaleTail
          by_cases hh : t ∈ {t | A < ∑ j, Real.log (1 + t j)}
          · simp [Set.indicator_of_mem hh, le_refl]
          · simp [Set.indicator_of_notMem hh]
            exact ht)
    _ ≤ _ := by rw [log_scale_tail_integral_reindex (Fintype.equivFinOfCardEq hcard).symm]; exact finite_log_scale_tail_integral_uniform hb hA

end

variable {n : ℕ} (hn : 2 ≤ n) (i : Fin n) {b : ℝ}

theorem spatial_scale_index_card : Fintype.card (SpatialScaleIndex i) = n - 1 := by
  simp

theorem spatial_scale_complement_integral_eq (b T : ℝ) :
    (∫ t in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1)) =
      ∫ t : SpatialScaleVector i in Ici 0, strictLogScaleTail b (2 * Real.log T) t := by
  change _ =
      ∫ t in Ici 0,
        ({t | 2 * Real.log T < ∑ j, Real.log (1 + t j)}).indicator
          (logScaleTail b (2 * Real.log T)) t
  have hm : MeasurableSet {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [integral_indicator hm, Measure.restrict_restrict hm]
  have hs : {t | 2 * Real.log T < ∑ j, Real.log (1 + t j)} ∩ Ici 0 =
      Ici 0 \ spatialScaleDomain i T := by
    ext t
    constructor
    · rintro ⟨hlog, ht⟩
      change _ < _ at hlog
      refine ⟨ht, ?_⟩
      intro hD
      have he : spatialScaleLogSum t = ∑ j, Real.log (1 + t j) := by
        apply Finset.sum_congr rfl
        intro j _
        have htj : 0 ≤ t j := ht j
        rw [max_eq_right htj]
      rw [← he] at hlog
      exact (not_lt_of_ge hD.2) hlog
    · rintro ⟨ht, hD⟩
      refine ⟨?_, ht⟩
      by_contra h
      apply hD
      refine ⟨ht, ?_⟩
      change _ ≤ _
      have hh : ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T := le_of_not_gt h
      convert hh using 1
      apply Finset.sum_congr rfl
      intro j _
      have htj : 0 ≤ t j := ht j
      rw [max_eq_right htj]
  rw [hs]
  apply setIntegral_congr_fun (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)
  intro t ht
  have hlog : 2 * Real.log T < ∑ j, Real.log (1 + t j) := by
    rw [← hs] at ht
    exact ht.1
  exact (if_pos hlog.le).symm

include hn in
theorem spatial_scale_complement_power_integrable (hb : 0 < b) (T : ℝ) :
    IntegrableOn (fun t => ∏ j, (1 + t j) ^ (-b - 1))
      (Ici 0 \ spatialScaleDomain i T) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by
    rw [spatial_scale_index_card]
    omega
  have h := (strict_log_scale_tail_integrable_of_card hcard hb (2 * Real.log T)).mono_set
    (Set.diff_subset : Ici 0 \ spatialScaleDomain i T ⊆ Ici 0)
  apply h.congr_fun _ (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)
  intro t ht
  have he : spatialScaleLogSum t = ∑ j, Real.log (1 + t j) := by
    apply Finset.sum_congr rfl
    intro j _
    have htj : 0 ≤ t j := ht.1 j
    rw [max_eq_right htj]
  have hlog : 2 * Real.log T < ∑ j, Real.log (1 + t j) := by
    by_contra hh
    apply ht.2
    refine ⟨ht.1, ?_⟩
    change _ ≤ _
    bound
  unfold strictLogScaleTail logScaleTail
  have hm : t ∈ {t | 2 * Real.log T < ∑ j, Real.log (1 + t j)} := hlog
  rw [Set.indicator_of_mem hm, ite_eq_left hlog.le]

include hn in
/-- The scale-domain complement estimate used by the actual cardinal
interpolation defect. The logarithmic power is one less than the number of
scales, exactly as required in the paper's interpolation bound. -/
theorem spatial_scale_complement_power_integral_le {T : ℝ} (hb : (1 / 2) ≤ b) (hT : 1 ≤ T) :
    (∫ t in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1)) ≤
      16 ^ (n - 1) * T ^ (-2 * b) * (1 + Real.log T) ^ (n - 2) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by
    rw [spatial_scale_index_card]
    omega
  have hlogT  := Real.log_nonneg hT
  rw [spatial_scale_complement_integral_eq]
  have h := strict_log_scale_tail_integral_le hcard hb (by linarith : 0 ≤ 2 * Real.log T)
  have he : Real.exp (-(b * (2 * Real.log T))) = T ^ (-2 * b) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    ring
  rw [he] at h
  have hpow : (1 + 2 * Real.log T) ^ (n - 2) ≤
      2 ^ (n - 2) * (1 + Real.log T) ^ (n - 2) := by
    have hh := pow_le_pow_left₀ (by positivity)
      (by linarith : 1 + 2 * Real.log T ≤ 2 * (1 + Real.log T)) (n - 2)
    simpa only [mul_pow] using hh
  have hconst : (8 : ℝ) ^ (n - 2 + 1) * 2 ^ (n - 2) ≤ 16 ^ (n - 1) := by
    have hn' : n - 2 + 1 = n - 1 := by omega
    rw [hn']
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (by omega : n - 2 ≤ n - 1)) (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  have hh := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 8 ^ (n - 2 + 1) * T ^ (-2 * b))
  have hc := mul_le_mul_of_nonneg_right hconst
    (by positivity : 0 ≤ T ^ (-2 * b) * (1 + Real.log T) ^ (n - 2))
  bound

end NearlyMinimax
