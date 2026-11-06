/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Rigidity.KernelTransform
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.OpenPos
import BergmanWeakType.Weighted.CompactIntegral
import BergmanWeakType.Rigidity.DiskSimilarity
import Mathlib.Tactic
import BergmanWeakType.Derivative




open Set MeasureTheory Metric

namespace BergmanWeakType


-- Keep the public statement's topology, bornology, and metric instances identical to the
-- independently elaborated Challenge statement, which imports no C*-algebra instances.
attribute [-instance] instCommCStarAlgebraComplex in
/-- Among bounded simply connected domains, positive weak constant one characterizes disks. -/
theorem positive_constant_eq_one_iff_disk (Ω : Set ℂ) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hconnected : IsSimplyConnected Ω) (K : ℂ → ℂ → ℂ) (hK : IsBergmanKernel Ω K) :
    weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) = 1 ↔
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = Metric.ball c R :=
  by
  constructor
  · intro hc
    by_contra hnd
    have : IsFiniteMeasure (area.restrict Ω) := isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
    obtain ⟨x, hx⟩ := hconnected.nonempty
    obtain ⟨ψ, hψ, hψbij, _⟩ := Complex.exists_bijOn_unitBall_map_eq_zero hopen hconnected hbounded hx
    let φ := Function.invFunOn ψ Ω
    have hinv := hψbij.invOn_invFunOn.symm
    have hbij := hψbij.symm hinv
    have hφ := differentiableOn_inverse hopen isOpen_ball hψ hinv.symm hbij.mapsTo
    let q := deriv φ
    have hne : ∀ z ∈ disk, q z ≠ 0 := fun z hz ↦
      right_ne_zero_of_mul_eq_one (deriv_inverse_mul isOpen_ball hopen hφ hψ hinv hbij.mapsTo hz)
    let r : ℝ := 1 / 2
    have hr : 0 < r := one_half_pos
    have hr1 : r < 1 := one_half_lt_one
    let A := ball (0 : ℂ) r
    let B := closedBall (0 : ℂ) 1
    have hC := isCompact_closedBall (0 : ℂ) r
    let F := fun ζ w ↦ q w * kernel ζ w
    have hsub : A ⊆ disk := ball_subset_ball hr1.le
    have hEopen : IsOpen (φ '' A) := by
      simp only [disk] at hsub
      rw [← inter_eq_left.mpr hsub, hinv.1.image_inter', hbij.image_eq, inter_comm]
      exact hψ.continuousOn.isOpen_inter_preimage hopen isOpen_ball
    have hEpos := hEopen.measure_pos area ⟨φ 0, 0, mem_ball_self hr, rfl⟩
    rw [← hbij.image_eq] at hbounded hnd
    have hq := (hφ.analyticOnNhd isOpen_ball).deriv.differentiableOn
    have hprod : ContinuousOn (fun p : ℂ × ℂ ↦ F p.1 p.2) (B ×ˢ closedBall 0 r) :=
      by
      refine (hq.continuousOn.comp continuous_snd.continuousOn ?_).mul ?_
      · exact fun p hp ↦ lt_of_le_of_lt hp.2 hr1
      · refine ((continuousOn_const.sub (continuous_fst.continuousOn.mul continuous_snd.star.continuousOn)).inv₀ ?_).pow 2
        intro p hp
        exact kernel_denominator_ne_zero_closed_left (by simp_all [B]) (lt_of_le_of_lt hp.2 hr1)
    have : IsFiniteMeasure (area.restrict A) :=
      isFiniteMeasure_restrict.mpr ((isBounded_ball  ).measure_lt_top).ne
    have hμ : ∀ᵐ w ∂area.restrict A, w ∈ closedBall 0 r :=
      (ae_restrict_mem isOpen_ball.measurableSet).mono fun _ hw ↦ ball_subset_closedBall hw
    have hFi ζ hζ :=
      ((hprod.uncurry_left (f := F) ζ hζ).integrableOn_compact (μ := area) hC).mono_set ball_subset_closedBall
    have hI :=
      Weighted.continuousOn_integral_mul_of_compact hC hμ (integrable_const (1 : ℂ)) 
        hprod
    have hJ :=
      Weighted.continuousOn_integral_mul_of_compact hC hμ (integrable_const (1 : ℝ)) (F :=
        fun ζ w ↦ ‖F ζ w‖) hprod.norm
    simp only [mul_one] at hI hJ
    let I := fun ζ ↦ ‖∫ w in A, F ζ w ∂area‖
    let J := fun ζ ↦ ∫ w in A, ‖F ζ w‖ ∂area
    have hpos : ∀ ζ ∈ B, 0 < J ζ := by
      intro ζ hζ
      apply (setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) (hFi ζ hζ).norm).mpr
      have hsub : A ⊆ Function.support (fun w ↦ ‖F ζ w‖) :=
        by
        intro w hw
        have hwd := lt_trans hw hr1
        simp [F, kernel, hne w hwd]
        exact kernel_denominator_ne_zero_closed_left (by simpa [B] using hζ) hwd
      rw [inter_eq_right.mpr hsub]
      exact?
    have hlt : ∀ ζ ∈ B, I ζ < J ζ := by
      intro ζ hζ
      have hζnorm : ‖ζ‖ ≤ 1 := by simp_all [B]
      have hle := norm_integral_le_integral_norm (F ζ) (μ := area.restrict A)
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hIne := norm_pos_iff.mp (heq.symm ▸ hpos ζ hζ)
      apply hnd
      have hderiv : ∀ w ∈ disk, q w * (1 - star ζ * w) ^ 2 = q 0 :=
        by
        let c := ∫ w in A, F ζ w ∂area
        let G := fun w ↦ q w * (1 - star ζ * w) ^ 2 / c
        have hBcont := hprod.uncurry_left (f := F) ζ hζ
        let g := fun w ↦ F ζ w / c
        have hg := (hFi ζ hζ).div_const c
        have hreal : (fun w ↦ (g w).re) =ᵐ[area.restrict A] (fun w ↦ ‖g w‖) :=
          by
          apply
            (integral_eq_iff_of_ae_le hg.re hg.norm (Filter.Eventually.of_forall fun w ↦ Complex.re_le_norm _)).mp
          have hp := (hpos ζ hζ).ne'
          rw [integral_re hg]
          simp_all [I, J, c, A, integral_div]
        have hGd : DifferentiableOn ℂ G disk := by fun_prop
        have hinner : ∀ w ∈ A, (G w).im = 0 := by
          intro w hw
          have hwd := lt_trans hw hr1
          have hd := kernel_denominator_ne_zero_closed_left hζnorm hwd
          have hform : G w = F ζ w / c * (Complex.normSq (1 - ζ * star w) ^ 2 : ℝ) :=
            by
            push_cast
            simp [← Complex.mul_conj]
            dsimp [G, kernel, F]
            simp only [← starRingEnd_apply] at hd ⊢
            field
          have him := (Measure.eqOn_open_of_ae_eq
            (hreal.mono fun w hw ↦ show (g w).im = 0 from Complex.abs_re_eq_norm.mp (by simpa using congrArg abs hw))
            isOpen_ball (Complex.continuous_im.comp_continuousOn ((hBcont.mono ball_subset_closedBall).div_const _))
            continuousOn_const) hw
          change (F ζ w / c).im = 0 at him
          rw [hform, Complex.mul_im, Complex.ofReal_im, him]
          ring
        obtain ⟨d, hd⟩ :=
          (hGd.analyticOnNhd isOpen_ball).mono hsub |>.eq_const_of_im_eq_const hinner isOpen_ball
            ⟨⟨0, mem_ball_self hr⟩, (convex_ball 0 r).isPreconnected⟩
        have hall :=
          (hGd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
            (convex_ball _ 1).isPreconnected (by simp_all)
            ((isOpen_ball.eventually_mem (mem_ball_self hr)).mono fun w hw ↦ hd w hw)
        intro w hw
        have hval : G w = G 0 := (hall hw).trans (hall (by simp_all)).symm
        grind
      have hden {w : ℂ} (hw : w ∈ disk) := by
        simpa using (star_ne_zero.mpr (kernel_denominator_ne_zero_closed_left hζnorm hw))
      let a := φ 0
      let b := q 0
      have hb := hne 0 (by continuity)
      let H := fun w ↦ a + b * w / (1 - star ζ * w)
      have hH : ∀ w ∈ disk, HasDerivAt H (q w) w := by
        intro w hw
        have hn := hden hw
        rw [(eq_div_iff (pow_ne_zero 2 hn)).mpr (hderiv w hw)]
        dsimp only [H]
        differentiate

      have heq :=
        image_congr
          (isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℂ) 1).isPreconnected hφ
            (fun w hw ↦ (hH w hw).differentiableAt.differentiableWithinAt) (fun w hw ↦ (hH w hw).deriv.symm) (x := 0)
            (by continuity) (by continuity))
      have hζlt :=
        lt_of_le_of_ne hζnorm fun hζeq ↦
          by
          obtain ⟨M, hM⟩ := (heq ▸ hbounded).exists_norm_le
          have hi t (ht : t ∈ Ioo 0 1) : ‖b‖ * t ≤ (M + ‖a‖) * (1 - t) := by
            have hw : (t : ℂ) * ζ ∈ disk := by simp_all [mem_disk_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
            have hh := (norm_sub_le (H ((t : ℂ) * ζ)) a).trans
              (add_le_add (hM _ ⟨_, hw, rfl⟩) le_rfl)
            dsimp only [H] at hh
            rw [add_sub_cancel_left, norm_div, norm_mul, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1, hζeq, mul_one,
              mul_left_comm (star ζ) (t : ℂ), Complex.star_def, Complex.conj_mul', hζeq, Complex.ofReal_one, one_pow, mul_one,
              ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.2)] at hh
            exact (div_le_iff₀ (sub_pos.mpr ht.2)).mp hh
          apply (norm_pos_iff.mpr hb).not_ge
          simpa using le_on_closure hi (by fun_prop) (by fun_prop)
            (by norm_num [closure_Ioo] : (1 : ℝ) ∈ closure (Ioo 0 1))
      let d := 1 - ‖ζ‖ ^ 2
      have hd : 0 < d := by aesop
      have hdc := Complex.ofReal_ne_zero.mpr hd.ne'
      let Z := Complex.UnitDisc.mk ζ hζlt
      let c := a + b * ζ / (d : ℂ)
      let s := b / (d : ℂ)
      have hs := div_ne_zero hb hdc
      have hform :
        ∀ W : Complex.UnitDisc, a + b * (W : ℂ) / (1 - star ζ * W) = c + s * (Complex.UnitDisc.shift (-Z) W : ℂ) :=
        by
        intro W
        have hn := hden (show (W : ℂ) ∈ disk from (mem_disk_iff _).mpr W.norm_lt_one)
        have hnorm := Complex.conj_mul' ζ
        dsimp [c, s]
        rw [Complex.UnitDisc.coe_shift]
        simp only [Z, Complex.UnitDisc.coe_neg, Complex.UnitDisc.coe_mk, map_neg, neg_mul, ← sub_eq_add_neg]
        field_simp [hn, hdc]
        dsimp [d]
        push_cast at hnorm ⊢
        grind
      have hrange (f : ℂ → ℂ) : f '' disk = range (fun w : Complex.UnitDisc ↦ f w) :=
        by
        ext z
        simp [Complex.UnitDisc.exists]
      have himage : (fun w ↦ a + b * w / (1 - star ζ * w)) '' disk = (fun w ↦ c + s * w) '' disk :=
        by
        rw [hrange, hrange]
        simpa only [Function.comp_def, ← hform] using
          (Complex.UnitDisc.shift (-Z)).surjective.range_comp (fun w : Complex.UnitDisc ↦ c + s * w)
      exact ⟨c, ‖s‖, norm_pos_iff.mpr hs, heq.trans (himage.trans (image_affine_disk hs))⟩
    obtain ⟨a, ha, hmax⟩ :=
      (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn ⟨0, by simp⟩ (hI.norm.div hJ (fun ζ hζ ↦ (hpos ζ hζ).ne'))
    let η := 1 - I a / J a
    have hη1 : η ≤ 1 := sub_le_self _ (div_nonneg (norm_nonneg _) (hpos a ha).le)
    let E := φ '' A
    have hgap : ∀ a ∈ Ω, ‖∫ w in E, K a w ∂area‖ ≤ (1 - η) * ∫ w in E, ‖K a w‖ ∂area :=
      by
      intro a ha
      obtain ⟨z, hz, rfl⟩ := hbij.surjOn ha
      simp only [η, sub_sub_cancel]
      convert div_le_div_of_nonneg_right ((div_le_iff₀ (hpos z (ball_subset_closedBall hz))).mp (hmax (ball_subset_closedBall hz))) (norm_nonneg (q z)) using 1
      all_goals
        first
        | rw [← norm_div]; congr 1
        | rw [mul_div_assoc]; congr 1
        rw [area_integral_image_eq isOpen_ball (hφ.mono hsub) (hbij.injOn.mono hsub), ← integral_div]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with w hw
      · exact?
      · simpa only [norm_smul, Real.norm_eq_abs, abs_sq, norm_div, smul_eq_mul] using
          congrArg norm (hK.disk_jacobian_formula hopen hφ hψ hbij hinv hz (hsub hw))
    have hE := hEopen.measurableSet
    have hsubE := (hbij.mapsTo.mono_left hsub).image_subset
    apply not_lt_of_ge hc.le
    let μ := area.restrict Ω
    have hre : μ.restrict E = area.restrict E := Measure.restrict_restrict_of_subset hsubE
    have hmeasure := Measure.restrict_eq_self area hsubE
    have hEr : 0 < μ.real E := ENNReal.toReal_pos (by grind) (measure_ne_top _ _)
    let f : ℂ → ℂ := fun w ↦ (1 - E.indicator (fun _ ↦ η) w : ℝ)
    have hnorm w : ‖f w‖ = 1 - E.indicator (fun _ ↦ η) w :=
      by
      rw [Complex.norm_real]
      by_cases hw : w ∈ E <;> simp [hw] <;> linarith
    have hmass {g : ℂ → ℝ} (hg : Integrable g μ) : ∫ w, g w * ‖f w‖ ∂μ = ∫ w, g w ∂μ - η * ∫ w in E, g w ∂μ :=
      by
      simp_rw [hnorm, mul_sub, mul_one, ← Set.indicator_mul_right E g _]
      rw [integral_sub hg ((hg.mul_const η).indicator hE), integral_indicator hE, integral_mul_const,
        mul_comm]
    have hf : Integrable f μ := ((integrable_const _).sub ((integrable_const η).indicator hE)).ofReal
    refine lt_of_lt_of_le ?_ (measure_univ_div_mass_le_weakTypeConstant_of_witness hf ?_)
    · apply (ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.one_ne_top) (Or.inr one_ne_zero)).2
      simp only [one_mul]
      have hmass := hmass  (integrable_const (1 : ℝ))
      simp only [one_mul, integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] at hmass
      rw [← ofReal_integral_norm_eq_lintegral_enorm hf, hmass]
      have hlt : μ.real univ - η * μ.real E < μ.real univ := sub_lt_self _ (mul_pos (sub_pos.mpr ((div_lt_one (hpos a ha)).mpr (hlt a ha))) hEr)
      have ho := (ENNReal.ofReal_lt_ofReal_iff (hEr.trans_le (measureReal_mono (subset_univ E)))).mpr hlt
      simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using ho
    · filter_upwards [ae_restrict_mem hopen.measurableSet] with a ha
      have hk := (hK.squareIntegrable a ha).integrable one_le_two
      have hg : ‖∫ w in E, K a w ∂μ‖ ≤ (1 - η) * ∫ w in E, ‖K a w‖ ∂μ := by simp_all
      have hout : 1 ≤ ∫ w, ‖K a w‖ * ‖f w‖ ∂μ :=
        by
        have hs := norm_add_le (∫ w in E, K a w ∂μ) (∫ w in Eᶜ, K a w ∂μ)
        rw [integral_add_compl hE hk, hK.integral_section_eq_one ha, norm_one] at hs
        have hc := norm_integral_le_integral_norm (μ := μ.restrict Eᶜ) (K a)
        rw [hmass hk.norm, ← integral_add_compl hE hk.norm]
        nlinarith
      have hle := (Real.ofReal_le_enorm _).trans (enorm_integral_le_lintegral_enorm (μ := μ) (fun w ↦ ‖K a w‖ * ‖f w‖))
      simpa only [ENNReal.ofReal_one, domainPositiveProjection, enorm_mul, enorm_norm, ofReal_norm] using
        (ENNReal.ofReal_le_ofReal hout).trans hle
  · rintro ⟨c, R, hR, rfl⟩
    exact?

end BergmanWeakType
