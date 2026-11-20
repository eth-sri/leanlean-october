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
    logScaleTail b A ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s) = logScaleTail b A s := by
  have hp := e.prod_comp (fun j : ι => (1 + ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s) j) ^ (-b - 1 : ℝ))
  simp only [MeasurableEquiv.piCongrLeft_apply_apply] at hp
  simp only [logScaleTail, orthant_reindex_sum e s (fun x => Real.log (1 + x)), ← hp]

theorem log_scale_tail_integral_reindex :
    (∫ t : ι → ℝ in Ici 0, logScaleTail b A t) =
      ∫ s : κ → ℝ in Ici 0, logScaleTail b A s := by
  rw [← (orthant_reindex_preserving e).integral_comp']
  exact integral_congr_ae (Filter.Eventually.of_forall (log_scale_tail_reindex e b A))

end

section
variable {m : ℕ} (hcard : Fintype.card ι = m + 1)
include hcard

theorem log_scale_tail_integrable_of_card
    {b : ℝ} (hb : 0 < b) (A : ℝ) :
    IntegrableOn (logScaleTail b A : (ι → ℝ) → ℝ) (Ici 0) := by
  let e := (Fintype.equivFinOfCardEq hcard).symm
  have hp := orthant_reindex_preserving e
  apply (hp.integrable_comp_emb (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e).measurableEmbedding).mp
  simpa only [IntegrableOn, Function.comp_def, log_scale_tail_reindex e b A] using finite_log_scale_tail_integrable (m := m) hb A

theorem log_scale_tail_integral_uniform_of_card
    {b A : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ t : ι → ℝ in Ici 0, logScaleTail b A t) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  rw [log_scale_tail_integral_reindex (Fintype.equivFinOfCardEq hcard).symm]
  exact finite_log_scale_tail_integral_uniform hb hA

end

def strictLogScaleTail (b A : ℝ) (t : ι → ℝ) : ℝ :=
  ({t : ι → ℝ | A < ∑ j, Real.log (1 + t j)}).indicator (logScaleTail b A) t

section
variable {m : ℕ} (hcard : Fintype.card ι = m + 1)
include hcard

theorem strict_log_scale_tail_integrable_of_card
    {b : ℝ} (hb : 0 < b) (A : ℝ) :
    IntegrableOn (strictLogScaleTail b A : (ι → ℝ) → ℝ) (Ici 0) := by
  exact (log_scale_tail_integrable_of_card hcard hb A).indicator
    (measurableSet_lt measurable_const (Finset.measurable_sum _ fun j _ =>
      Real.measurable_log.comp (measurable_const.add (measurable_pi_apply j))))

theorem strict_log_scale_tail_integral_le
    {b A : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ t : ι → ℝ in Ici 0, strictLogScaleTail b A t) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  have hbpos : 0 < b := by linarith
  refine (integral_mono_ae (strict_log_scale_tail_integrable_of_card hcard hbpos A)
    (log_scale_tail_integrable_of_card hcard hbpos A) ?_).trans
    (log_scale_tail_integral_uniform_of_card hcard hb hA)
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ici (a := (0 : ι → ℝ)))] with t ht
  exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => by
    unfold logScaleTail
    split_ifs
    · exact Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by have hj : (0 : ℝ) ≤ t j := ht j; positivity) _
    · rfl)

end

section
variable {n : ℕ}

theorem spatial_scale_index_card (i : Fin n) : Fintype.card (SpatialScaleIndex i) = n - 1 := by
  simp_all

theorem spatial_scale_domain_original (i : Fin n) (T : ℝ) :
    spatialScaleDomain i T = Ici 0 ∩
      {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T} := by
  ext t
  change ((0 : SpatialScaleVector i) ≤ t ∧ _) ↔ ((0 : SpatialScaleVector i) ≤ t ∧ _)
  refine and_congr_right fun ht => ?_
  change spatialScaleLogSum i t ≤ _ ↔ _
  have he : (fun j => max 0 (t j)) = t := funext fun j => max_eq_right (ht j)
  simp only [spatialScaleLogSum, congrFun he, Set.mem_ofPred_eq]

private theorem spatial_scale_complement (i : Fin n) (T : ℝ) :
    Ici 0 \ spatialScaleDomain i T =
      {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} ∩ Ici 0 := by
  rw [spatial_scale_domain_original]
  ext t
  simp only [mem_diff, mem_inter_iff, mem_setOf_eq, not_and, not_le]
  tauto

theorem spatial_scale_complement_integral_eq (i : Fin n) (b T : ℝ) :
    (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) =
      ∫ t : SpatialScaleVector i in Ici 0, strictLogScaleTail b (2 * Real.log T) t := by
  have hm : MeasurableSet {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} :=
    measurableSet_lt measurable_const (by fun_prop)
  unfold strictLogScaleTail
  rw [integral_indicator hm, Measure.restrict_restrict hm, ← spatial_scale_complement]
  refine setIntegral_congr_fun (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet) ?_
  intro t ht
  rw [spatial_scale_complement] at ht
  exact (if_pos (le_of_lt ht.1)).symm

theorem spatial_scale_complement_power_integrable (hn : 2 ≤ n) (i : Fin n)
    {b : ℝ} (hb : 0 < b) (T : ℝ) :
    IntegrableOn (fun t : SpatialScaleVector i => ∏ j, (1 + t j) ^ (-b - 1 : ℝ))
      (Ici 0 \ spatialScaleDomain i T) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by
    rw [spatial_scale_index_card]
    omega
  have h := (strict_log_scale_tail_integrable_of_card hcard hb (2 * Real.log T)).mono_set
    (Set.diff_subset : Ici (0 : SpatialScaleVector i) \ spatialScaleDomain i T ⊆ Ici 0)
  apply h.congr_fun _ (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)
  intro t ht
  rw [spatial_scale_complement] at ht
  rw [strictLogScaleTail, Set.indicator_of_mem ht.1, logScaleTail, if_pos (le_of_lt ht.1)]

/-- The scale-domain complement estimate used by the actual cardinal
interpolation defect. The logarithmic power is one less than the number of
scales, exactly as required in the paper's interpolation bound. -/
theorem spatial_scale_complement_power_integral_le (hn : 2 ≤ n) (i : Fin n)
    {b T : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hT : 1 ≤ T) :
    (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) ≤
      16 ^ (n - 1) * T ^ (-2 * b : ℝ) * (1 + Real.log T) ^ (n - 2) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by
    rw [spatial_scale_index_card]
    omega
  have hlogT := Real.log_nonneg hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  rw [spatial_scale_complement_integral_eq]
  have h := strict_log_scale_tail_integral_le hcard hb (by linarith : 0 ≤ 2 * Real.log T)
  have he : Real.exp (-(b * (2 * Real.log T))) = T ^ (-2 * b : ℝ) := by
    simp [Real.rpow_def_of_pos hTpos] <;> ring
  rw [he] at h
  have hpow : (1 + 2 * Real.log T) ^ (n - 2) ≤
      (2 : ℝ) ^ (n - 2) * (1 + Real.log T) ^ (n - 2) := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 2 * Real.log T)
      (by linarith : 1 + 2 * Real.log T ≤ 2 * (1 + Real.log T)) (n - 2)
    simpa only [mul_pow] using hh
  have hconst : (8 : ℝ) ^ (n - 2 + 1) * 2 ^ (n - 2) ≤ 16 ^ (n - 1) := by
    have hn' : n - 2 + 1 = n - 1 := by omega
    rw [hn']
    calc
      _ ≤ 8 ^ (n - 1) * 2 ^ (n - 1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n - 2 ≤ n - 1)) (by positivity)
      _ = _ := by norm_num [← mul_pow]
  have hh := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ (8 : ℝ) ^ (n - 2 + 1) * T ^ (-2 * b : ℝ))
  have hc := mul_le_mul_of_nonneg_right hconst
    (by positivity : 0 ≤ T ^ (-2 * b : ℝ) * (1 + Real.log T) ^ (n - 2))
  calc
    _ ≤ _ := h
    _ ≤ _ := by nlinarith [hh, hc]

/-- Fubini and the orthant tail bound for a dominated family of spatial sections. -/
theorem spatial_scale_tail_prod_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (hn : 2 ≤ n) (i : Fin n) {b T C : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hT : 1 ≤ T) (hC : 0 ≤ C)
    {S : Set (SpatialScaleVector i)} (hS : MeasurableSet S)
    (hsub : S ⊆ Ici 0 \ spatialScaleDomain i T)
    {f : SpatialScaleVector i × Ω → ℝ} (hf : Integrable f ((volume.restrict S).prod ν))
    (hdom : ∀ t ∈ Ici 0,
      (∫ y, f (t,y) ∂ν) ≤ C ^ Fintype.card (SpatialScaleIndex i) * ∏ j, (1+t j)^(-b-1 : ℝ)) :
    (∫ y, (∫ t in S, f (t,y)) ∂ν) ≤
      (16*C)^(n-1) * T^(-2*b : ℝ) * (1+Real.log T)^(n-2) := by
  rw [← integral_prod_symm _ hf, integral_prod _ hf]
  let P : SpatialScaleVector i → ℝ := fun t => ∏ j, (1+t j)^(-b-1 : ℝ)
  have hP : IntegrableOn P (Ici 0 \ spatialScaleDomain i T) :=
    spatial_scale_complement_power_integrable hn i (show 0 < b by linarith) T
  have hmono := integral_mono_ae hf.integral_prod_left ((hP.mono_set hsub).const_mul
    (C ^ Fintype.card (SpatialScaleIndex i))) ((ae_restrict_mem hS).mono fun t ht => hdom t (hsub ht).1)
  rw [integral_const_mul] at hmono
  apply hmono.trans
  have hP0 : ∀ᵐ t ∂volume.restrict (Ici 0 \ spatialScaleDomain i T), 0 ≤ P t := by
    filter_upwards [ae_restrict_mem (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)] with t ht
    exact Finset.prod_nonneg fun j _ => Real.rpow_nonneg (le_trans (by norm_num) (le_add_of_nonneg_right
      (show (0 : ℝ) ≤ t j from ht.1 j))) _
  have h := (integral_mono_measure (Measure.restrict_mono_set _ hsub) hP0 hP).trans
    (spatial_scale_complement_power_integral_le hn i hb hT)
  simpa only [spatial_scale_index_card, mul_pow, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left h (pow_nonneg hC _)

end

end NearlyMinimax
