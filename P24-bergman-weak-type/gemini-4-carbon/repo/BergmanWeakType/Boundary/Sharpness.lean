module

public import BergmanWeakType.Measure
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

noncomputable section

open MeasureTheory Set Real Filter Metric
open scoped ENNReal Topology

namespace BergmanWeakType

theorem column_le_weakBound {α L : ℝ} {C : ℝ≥0∞} (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) C)
    {a : ℂ} (ha : a ∈ disk) {E : Set ℂ} (hE : E ⊆ disk)
    (hcol : ∀ z ∈ E, L ≤ ‖weightedKernel α z a‖) (hL : 0 < L) :
    ENNReal.ofReal L * weightedArea α E ≤ C := by
  let := weightedArea_isProbabilityMeasure α hα
  refine le_of_tendsto (((ENNReal.continuous_mul_const (measure_ne_top _ _)).comp
    ENNReal.continuous_ofReal).continuousAt.tendsto.mono_left
      (show 𝓝[<] L ≤ 𝓝 L from nhdsWithin_le_nhds)) ?_
  filter_upwards [Ioo_mem_nhdsLT hL] with ℓ ⟨hℓ, hℓL⟩
  let R := (1 + ‖a‖) / 2
  have ha' : ‖a‖ < 1 := (mem_disk_iff a).mp ha
  have hcont : ContinuousOn (fun u : ℂ ↦ (1 - u) ^ (-(α + 2) : ℂ)) (closedBall 0 R) :=
    (continuous_const.sub continuous_id).continuousOn.cpow_const fun u hu ↦
      Complex.mem_slitPlane_iff.mpr <| Or.inl <| by
        simp only [Pi.sub_apply, id_eq, Complex.sub_re, Complex.one_re]
        dsimp [R] at hu; linarith [Complex.re_le_norm u, mem_closedBall_zero_iff.mp hu]
  obtain ⟨δ, hδ, hclose⟩ := uniformContinuousOn_iff.mp
    ((isCompact_closedBall 0 R).uniformContinuousOn_of_continuous hcont) ((L - ℓ) / 2) (by linarith)
  let r := min δ (R - ‖a‖)
  have hr : 0 < r := lt_min hδ (by dsimp [R]; linarith)
  have hsub_d : ball a r ⊆ disk := fun w hw ↦ (mem_disk_iff w).mpr <| by
    have : r ≤ R - ‖a‖ := min_le_right _ _
    dsimp [R] at this; linarith [mem_ball_iff_norm.mp hw, norm_sub_norm_le w a]
  let s := ball a r
  let f : ℂ → ℂ := s.indicator 1
  let m := (weightedArea α).real s
  have hs : MeasurableSet s := isOpen_ball.measurableSet
  have hspos : 0 < weightedArea α s := pos_iff_ne_zero.mpr fun h ↦ by
    have hd := withDensity_absolutelyContinuous' (μ := diskArea) (by fun_prop)
      (ae_mem_disk.mono fun z hz ↦ ne_of_gt <| ENNReal.ofReal_pos.mpr <|
        mul_pos (by linarith) (rpow_pos_of_pos (by nlinarith [(mem_disk_iff z).mp hz, norm_nonneg z]) _)) h
    rw [diskArea, Measure.restrict_eq_self _ hsub_d] at hd
    exact (measure_ball_pos area a hr).ne' hd
  have hsfinite : weightedArea α s ≠ ∞ := measure_ne_top _ _
  have hm : 0 < m := ENNReal.toReal_pos hspos.ne' hsfinite
  have hsub : E ⊆ {z | ENNReal.ofReal (ℓ * m) < ‖weightedProjection α f z‖ₑ} := fun z hz ↦ by
    have hz1 : ‖z‖ ≤ 1 := ((mem_disk_iff z).mp (hE hz)).le
    have hK : Integrable (weightedKernel α z) (weightedArea α) := by
      simpa only [mul_one] using integrable_weightedKernel_mul hα (integrable_const (1 : ℂ)) (hE hz)
    have herr : ‖weightedProjection α f z - (m : ℂ) * weightedKernel α z a‖ ≤ (L - ℓ) / 2 * m := by
      rw [weightedProjection,
        integral_congr_ae (.of_forall fun w ↦ show weightedKernel α z w * f w =
          s.indicator (weightedKernel α z) w by by_cases hw : w ∈ s <;> simp [f, hw]),
        integral_indicator hs, ← Complex.real_smul, ← setIntegral_const,
        ← integral_sub hK.integrableOn (integrable_const _)]
      refine norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun w hw ↦ ?_
      have hw' : ‖w - a‖ < r := mem_ball_iff_norm.mp hw
      have hmul {u : ℂ} (hu : ‖u‖ ≤ R) : z * star u ∈ closedBall 0 R :=
        mem_closedBall_zero_iff.mpr (by simpa using (mul_le_of_le_one_left (norm_nonneg u) hz1).trans hu)
      have hdist : dist (z * star w) (z * star a) < δ := by
        rw [dist_eq_norm, ← mul_sub, ← star_sub, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt (hw'.trans_le (min_le_left _ _))
      simpa only [weightedKernel, dist_eq_norm] using (hclose _
        (hmul (by linarith [hw'.trans_le (min_le_right _ _), norm_sub_norm_le w a]))
        _ (hmul (by dsimp [R]; linarith)) hdist).le
    have hrev := norm_sub_norm_le ((m : ℂ) * weightedKernel α z a) (weightedProjection α f z)
    rw [norm_sub_rev] at herr
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm] at hrev
    have hout : ℓ * m < ‖weightedProjection α f z‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (hcol z hz) hm.le]
    change ENNReal.ofReal (ℓ * m) < ‖weightedProjection α f z‖ₑ
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos hℓ hm).trans hout)).mpr hout
  have hb := (mul_le_mul_right (measure_mono hsub) (ENNReal.ofReal (ℓ * m))).trans <| by
    simpa [f, enorm_indicator_eq_indicator_enorm, hs] using
      hC f ((integrable_const (1 : ℂ)).indicator hs) (ℓ * m) (mul_pos hℓ hm)
  rw [ENNReal.ofReal_mul hℓ.le, show ENNReal.ofReal m = weightedArea α s from
    ENNReal.ofReal_toReal hsfinite, mul_assoc, mul_comm (weightedArea α s), ← mul_assoc] at hb
  exact (ENNReal.mul_le_mul_iff_left hspos.ne' hsfinite).mp hb

theorem one_le_weightedProjection_constant (α : ℝ) (hα : -1 < α) :
    1 ≤ weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  let := weightedArea_isProbabilityMeasure α hα
  refine le_sInf fun C hC ↦ ?_
  have hd : weightedArea α disk = 1 :=
    measure_univ (μ := weightedArea α) ▸ measure_congr (ae_eq_univ.mpr (ae_mem_disk_weightedArea α))
  simpa [hd] using column_le_weakBound hα hC (a := 0) (by simp [disk]) Subset.rfl
    (L := 1) (fun _ _ ↦ by simp [weightedKernel]) one_pos

theorem boundaryConstant_le_weightedProjection_constant (α : ℝ) (hα : 0 ≤ α) :
    ENNReal.ofReal (boundaryConstant α) ≤
      weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  have hα' : -1 < α := by linarith
  let := weightedArea_isProbabilityMeasure α hα'
  let cap (R : ℝ) : Set ℂ := disk ∩ ball 1 R
  let prof (R : ℝ) (u : ℂ) : ℝ :=
    if R * ‖u‖ ^ 2 < 2 * u.re then (2 * u.re - R * ‖u‖ ^ 2) ^ α else 0
  have hm_cap (R : ℝ) : Measurable (prof R) :=
    Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop) measurable_const
  have hb_cap {R : ℝ} (hR : 0 ≤ R) : ∀ᵐ u ∂diskArea, ‖prof R u‖ ≤ (2 : ℝ) ^ α :=
    ae_mem_disk.mono fun u hu ↦ by
      dsimp only [prof]
      split_ifs with h
      · rw [Real.norm_of_nonneg (rpow_nonneg (by linarith) _)]
        exact rpow_le_rpow (by linarith)
          (by nlinarith [(mem_disk_iff u).mp hu, Complex.re_le_norm u, mul_nonneg hR (sq_nonneg ‖u‖)]) hα
      · norm_num; positivity
  have hint0 : (∫ z, prof 0 z ∂diskArea) = gammaConstant α / (α + 2) := by
    rw [integral_diskArea_eq_circleAverage
      ((integrable_const _).mono' (hm_cap 0).aestronglyMeasurable (hb_cap le_rfl))]
    trans gammaConstant α * ∫ r in Ioo (0 : ℝ) 1, r ^ (α + 1)
    · rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
      have hcavg : circleAverage (prof 0) 0 r = r ^ α * gammaConstant α / 2 := by
        rw [circleAverage_eq_integral_add (-(π / 2)), smul_eq_mul,
          intervalIntegral.integral_of_le two_pi_pos.le,
          integral_congr_ae (g := (Ioc 0 π).indicator fun θ ↦ (2 * r) ^ α * sin θ ^ α) <| by
            refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
            filter_upwards [(show ∀ᵐ θ : ℝ, θ ≠ π by rw [ae_iff]; simp).and
              (show ∀ᵐ θ : ℝ, θ ≠ 2 * π by rw [ae_iff]; simp)] with θ hθ ⟨h0, h2pi⟩
            dsimp only [prof]
            rw [zero_mul, sub_zero, circleMap_zero_re, ← sub_eq_add_neg, cos_sub_pi_div_two]
            by_cases hpi : θ ≤ π
            · have hs := sin_pos_of_pos_of_lt_pi h0 (lt_of_le_of_ne hpi hθ.1)
              rw [indicator_of_mem (show θ ∈ Ioc 0 π from ⟨h0, hpi⟩),
                ite_eq_left (mul_pos zero_lt_two (mul_pos hr.1 hs)),
                show 2 * (r * sin θ) = (2 * r) * sin θ by ring,
                mul_rpow (mul_nonneg zero_le_two hr.1.le) hs.le]
            · have hs : sin θ ≤ 0 := by
                simpa using sin_nonpos_of_nonpos_of_neg_pi_le
                  (show θ - 2 * π ≤ 0 by linarith) (show -π ≤ θ - 2 * π by linarith)
              rw [indicator_of_notMem (by simp [hpi]),
                ite_eq_right (not_lt.mpr (by nlinarith [hr.1]))],
          setIntegral_indicator measurableSet_Ioc,
          inter_eq_right.mpr (Ioc_subset_Ioc_right (by linarith [pi_pos])),
          ← intervalIntegral.integral_of_le pi_pos.le, intervalIntegral.integral_const_mul,
          mul_rpow zero_le_two hr.1.le,
          show (2 : ℝ) ^ α * r ^ α * (∫ θ in 0..π, sin θ ^ α) =
            r ^ α * ((2 : ℝ) ^ α * ∫ θ in 0..π, sin θ ^ α) by ring,
          two_rpow_mul_integral_sin_rpow hα']
        field_simp [pi_pos.ne']
      rw [hcavg, smul_eq_mul, rpow_add hr.1, rpow_one]; ring
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
        integral_rpow (Or.inl (by linarith : -1 < α + 1)), one_rpow,
        zero_rpow (by linarith : α + 1 + 1 ≠ 0), sub_zero]; ring
  have hresc_eq {R : ℝ} (hR : 0 < R) :
      R ^ (-(α + 2)) * (weightedArea α).real (cap R) = (α + 1) * ∫ u, prof R u ∂diskArea := by
    have hsq (u : ℂ) : ‖1 - (R : ℂ) * u‖ ^ 2 = 1 - 2 * R * u.re + R ^ 2 * ‖u‖ ^ 2 := by
      simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hcap (u : ℂ) : 1 - (R : ℂ) * u ∈ cap R ↔ u ∈ disk ∧ R * ‖u‖ ^ 2 < 2 * u.re := by
      have hd : 1 - (R : ℂ) * u ∈ disk ↔ R * ‖u‖ ^ 2 < 2 * u.re := by
        rw [mem_disk_iff]; constructor <;> intro h <;> nlinarith [hsq u, norm_nonneg (1 - (R : ℂ) * u)]
      have hb : 1 - (R : ℂ) * u ∈ ball 1 R ↔ u ∈ disk := by
        rw [mem_ball, dist_eq_norm, show 1 - (R : ℂ) * u - 1 = -((R : ℂ) * u) by ring,
          norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le, mem_disk_iff]
        exact mul_lt_iff_lt_one_right hR
      simp [cap, hd, hb, and_comm]
    have hind (u : ℂ) : (cap R).indicator (fun z ↦ (1 - ‖z‖ ^ 2) ^ α) (1 - (R : ℂ) * u) =
        R ^ α * disk.indicator (prof R) u := by
      by_cases hu : u ∈ disk
      · rw [indicator_of_mem hu]; dsimp only [prof]
        by_cases hp : R * ‖u‖ ^ 2 < 2 * u.re
        · rw [indicator_of_mem ((hcap u).mpr ⟨hu, hp⟩), ite_eq_left hp, hsq,
            show 1 - (1 - 2 * R * u.re + R ^ 2 * ‖u‖ ^ 2) = R * (2 * u.re - R * ‖u‖ ^ 2) by ring,
            mul_rpow hR.le (by linarith)]
        · rw [indicator_of_notMem (by simpa [hcap u, hu] using hp), ite_eq_right hp, mul_zero]
      · rw [indicator_of_notMem hu, mul_zero, indicator_of_notMem fun h ↦ hu ((hcap u).mp h).1]
    have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
      (fun z : ℂ ↦ (cap R).indicator (fun z ↦ (1 - ‖z‖ ^ 2) ^ α) (1 - z)) R (hR := hR.le)
    rw [Complex.finrank_real_complex, integral_sub_left_eq_self _ volume 1] at hc
    simp only [Complex.real_smul, smul_eq_mul] at hc
    have hmass : (weightedArea α).real (cap R) =
        (α + 1) * (R ^ 2 * (R ^ α * ∫ u, prof R u ∂diskArea)) := by
      rw [← integral_indicator_one (measurableSet_disk.inter isOpen_ball.measurableSet),
        integral_weightedArea_eq_diskArea hα', diskArea, ← integral_indicator measurableSet_disk,
        ← integral_indicator measurableSet_disk, ← integral_const_mul (R ^ α)]
      simp_rw [← hind]
      simp only [area, integral_smul_measure, ENNReal.toReal_ofReal (by positivity : 0 ≤ π⁻¹), smul_eq_mul]
      rw [hc]
      conv_rhs => rw [show ∀ I : ℝ, (α + 1) * (R ^ 2 * (π⁻¹ * ((R ^ 2)⁻¹ * I))) = π⁻¹ * ((α + 1) * I)
        from fun _ ↦ by field_simp [hR.ne']]
      rw [← integral_const_mul (α + 1)]
      congr 1; refine integral_congr_ae (.of_forall fun z ↦ ?_)
      dsimp only [cap]
      by_cases hz : z ∈ disk ∩ ball 1 R
      · simp [hz, hz.1]
      · by_cases hzd : z ∈ disk <;> simp [hz, hzd]
    have hp : R ^ (-(α + 2)) * R ^ α * R ^ 2 = 1 := by
      rw [← rpow_add hR, ← rpow_natCast R 2, Nat.cast_ofNat, ← rpow_add hR,
        show -(α + 2) + α + 2 = 0 by ring, rpow_zero]
    rw [hmass]
    linear_combination (α + 1) * (∫ u, prof R u ∂diskArea) * hp
  have hcap_lim := tendsto_integral_filter_of_dominated_convergence (μ := diskArea)
    (F := prof) (f := prof 0) (l := 𝓝[>] (0 : ℝ)) (fun _ ↦ (2 : ℝ) ^ α)
    (.of_forall fun R ↦ (hm_cap R).aestronglyMeasurable)
    (mem_of_superset self_mem_nhdsWithin fun _ (hR : 0 < _) ↦ hb_cap hR.le)
    (integrable_const _) (.of_forall fun u ↦ by
      by_cases hu : 0 < u.re
      · have hb : Tendsto (fun R : ℝ ↦ 2 * u.re - R * ‖u‖ ^ 2) (𝓝[>] 0) (𝓝 (2 * u.re)) := by
          simpa using ((by fun_prop : Continuous fun R : ℝ ↦ 2 * u.re - R * ‖u‖ ^ 2).continuousAt
            (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
        dsimp only [prof]
        rw [zero_mul, sub_zero, ite_eq_left (by linarith)]
        refine (hb.rpow_const (Or.inl (by positivity))).congr' ?_
        filter_upwards [hb.eventually (lt_mem_nhds (by positivity : 0 < 2 * u.re))] with R hR
        exact (ite_eq_left (by linarith)).symm
      · dsimp only [prof]
        rw [zero_mul, sub_zero, ite_eq_right (by linarith)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with R (hR : 0 < R)
        exact (ite_eq_right (not_lt.mpr (by nlinarith [not_lt.mp hu, mul_nonneg hR.le (sq_nonneg ‖u‖)]))).symm)
  have hresc := (hcap_lim.const_mul (α + 1)).congr' <|
    mem_of_superset (self_mem_nhdsWithin (s := Ioi 0)) fun _ hR ↦ (hresc_eq hR).symm
  rw [hint0, show (α + 1) * (gammaConstant α / (α + 2)) = boundaryConstant α by
    unfold boundaryConstant; ring] at hresc
  refine le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hresc) ?_
  filter_upwards [self_mem_nhdsWithin] with R (hR : 0 < R)
  dsimp only [Function.comp_def]
  rw [ENNReal.ofReal_mul (rpow_nonneg hR.le _), measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine le_sInf fun C hC ↦ ?_
  have hp : Tendsto (fun t : ℝ ↦ (R + 1 - t) ^ (-(α + 2))) (𝓝[<] 1) (𝓝 (R ^ (-(α + 2)))) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (R + 1 - t) ^ (-(α + 2))) 1 :=
      (continuous_const.sub continuous_id).continuousAt.rpow_const
        (Or.inl (by change R + 1 - 1 ≠ 0; linarith))
    simpa only [add_sub_cancel_right] using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto ((ENNReal.continuous_mul_const
    (measure_ne_top (weightedArea α) (cap R))).continuousAt.tendsto.comp
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp)) ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
  have ha : (t : ℂ) ∈ disk := by simp [abs_of_pos ht.1, ht.2]
  refine column_le_weakBound hα' hC ha inter_subset_left (fun z hz ↦ ?_)
    (rpow_pos_of_pos (by linarith [ht.2]) _)
  rw [norm_weightedKernel]
  refine rpow_le_rpow_of_nonpos
    ((sub_pos.mpr ((mem_disk_iff z).mp hz.1)).trans_le (kernel_denominator_norm_lower z ha)) ?_
    (by linarith)
  rw [show 1 - z * star (t : ℂ) = (1 - z) + ((1 - t : ℝ) : ℂ) * z by push_cast; simp; ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr ht.2.le)]
  nlinarith [((mem_disk_iff z).mp hz.1).le,
    show ‖1 - z‖ < R by simpa [dist_eq_norm, norm_sub_rev] using hz.2, ht.2, norm_nonneg z]

end BergmanWeakType
