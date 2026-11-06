/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Weighted.PolarPotential
import BergmanWeakType.Weighted.SmoothCap
import BergmanWeakType.Weighted.NormalizerRadial
import Mathlib.Tactic

variable {α : ℝ} {f : ℂ → ℂ}

/-! # Weighted positive potentials and their normalized circular caps -/



noncomputable section

open MeasureTheory Real


namespace BergmanWeakType.Weighted

section
variable (α f) (z : ℂ)

def weightedPotential : ℝ :=
  ∫ w, ‖weightedKernel α z w‖ * ‖f w‖ ∂weightedArea α

def weightedNormalizedPotential : ℝ :=
  weightedPotential α f z / normalizer α ‖z‖

end

theorem measurable_weightedNormalizedPotential (hf : Integrable f (weightedArea α)) :
    Measurable (weightedNormalizedPotential α f) :=
  by
  apply Measurable.div
  · have hi : Measurable fun p : ℂ × ℂ ↦ ‖weightedKernel α p.1 p.2‖ * ‖hf.aestronglyMeasurable.mk f p.2‖ :=
      by
      simp_rw [norm_weightedKernel]
      fun_prop
    convert hi.stronglyMeasurable.integral_prod_right' (ν := weightedArea α).measurable using 1
    ext z
    apply integral_congr_ae
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with w hw
    simp [hw]
  · exact (measurable_normalizer α).comp measurable_norm

/-- Normalizing by the exact circular kernel average makes every capped circular mean
of an admissible weighted potential decrease with radius. -/
theorem antitoneOn_circleAverage_min_weightedNormalizedPotential (hf : Integrable f (weightedArea α)) (c : ℝ) :
    AntitoneOn (fun r ↦ circleAverage (fun z ↦ min (weightedNormalizedPotential α f z) c) 0 r) unitIco :=
  by
  have hsource {w : ℂ} (hw : w ∈ Metric.closedBall 0 1) :=
    (sq_le_one_iff₀ (norm_nonneg w)).mpr (show ‖w‖ ≤ 1 by simpa using hw)
  let P := fun H ↦ polarIntegral H id (weightedArea α) (fun w ↦ ‖f w‖)
  have hK := isCompact_closedBall (0 : ℂ) 1
  have hμ := (ae_mem_disk_weightedArea α).mono fun _ hw ↦ Metric.ball_subset_closedBall hw
  have hr2 {r} (hr : r ∈ unitIoo) := (sq_lt_one_iff₀ hr.1.le).mpr hr.2
  refine
    AntitoneOn.congr (f₁ := angularMean (fun r θ ↦ min (P (polarKernel (-(α + 2) / 2)) r θ / normalizer α r) c)) ?_ ?_
  · let k := α + 2
    let J := normalizer α
    let q := -k / 2
    let F := P (polarKernel q)
    let Fr := P (polarKernelR q)
    let Frr := P (polarKernelRR q)
    let Ft := P (polarKernelT q)
    let Ftt := P (polarKernelTT q)
    have h :=
      polarIntegral_regular hK hμ hf.norm continuousOn_id
        (@hsource) q
    let Jr := fun r ↦ boundaryIntegral (polarKernelR q) r 0
    let Jrr := fun r ↦ boundaryIntegral (polarKernelRR q) r 0
    have N := polarIntegral_regular isCompact_Icc (ae_restrict_mem measurableSet_Icc)
      integrable_boundaryDensity (continuous_circleMap 0 1).continuousOn
      (fun t _ ↦ by simp) q
    have hJ := continuousOn_normalizer α
    have hJr := N.hFr.uncurry_right 0 (Set.mem_univ _)
    have hJrr := N.hFrr.uncurry_right 0 (Set.mem_univ _)
    have hJd (r) (hr : r ∈ unitIoo) := by
      simpa only [q, k, polarIntegral_boundary_eq_normalizer] using N.hFd r hr 0
    have hJrd := (N.hFrd · · 0)
    have hJpos {r} (hr : r ∈ unitIco) : 0 < J r := normalizer_pos (by grind)
    have hJode (r) (hr : r ∈ unitIoo) :
        polarOperator k r (J r) (Jr r) (Jrr r) 0 = 0 := by
      have ht θ :=
        ((N.hFdt r hr θ).congr_of_eventuallyEq (.of_forall fun t ↦
          (polarIntegral_boundary_eq_normalizer α r t).symm)).unique
            (hasDerivAt_const θ (normalizer α r))
      have htt :=
        ((N.hFtd r hr 0).congr_of_eventuallyEq (.of_forall fun t ↦ (ht t).symm)).unique
          (hasDerivAt_const 0 0)
      dsimp only [q, k] at htt
      have hr2 := hr2 hr
      convert polarIntegral_operator isCompact_Icc (ae_restrict_mem measurableSet_Icc)
        integrable_boundaryDensity (continuous_circleMap 0 1).continuousOn
        (fun t _ ↦ by simp) (α + 2) q hr2 0 using 1
      · dsimp [J, Jr, Jrr, q, k, boundaryIntegral]
        simp only [polarOperator, polarIntegral_boundary_eq_normalizer, htt, zero_div, add_zero]
      · symm
        apply integral_eq_zero_of_ae
        filter_upwards [] with t
        rw [polarKernel_equation (α + 2) (circleMap 0 1 t) r 0
          (polarDenominator_pos hr2 (by simp) 0)
          hr.1.ne' (sub_pos.mpr hr2).ne']
        simp
    simp only [polarOperator, zero_div, add_zero] at hJode
    rcases h with ⟨hF⟩
    let Q := fun r θ ↦ F r θ / J r
    let Qr := fun r θ ↦ (Fr r θ - Q r θ * Jr r) / J r
    let Qrr := fun r θ ↦ (Frr r θ - Q r θ * Jrr r - 2 * Qr r θ * Jr r) / J r
    let W := fun r ↦ (1 - r ^ 2) ^ k * J r ^ 2
    let W' := fun r ↦ W r * (-(2 * k * r / (1 - r ^ 2)) + 2 * Jr r / J r)
    suffices H : ∀ ε > 0,
        AntitoneOn (angularMean (fun r θ ↦ smoothCap ε c (Q r θ))) unitIco by
      refine antitoneOn_of_frequently_antitoneOn_of_tendsto
        (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (Filter.Eventually.frequently (eventually_mem_nhdsWithin.mono fun ε hε ↦ H ε hε)) ?_
      intro r hr
      have hcont := (continuousOn_univ.mp (hF.uncurry_left r hr)).div_const (J r)
      have hc : Continuous fun ε ↦ angularMean (fun ε θ ↦ smoothCap ε c (Q r θ)) ε := by
        dsimp [angularMean, smoothCap]
        fun_prop
      simpa only [angularMean, smoothCap_zero] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    intro ε hε
    let d₁ := smoothCapInputDeriv ε c
    let d₂ := smoothCapSecondDeriv ε c
    apply
      antitoneOn_angularMean_of_polar_flux (Fr := fun r θ ↦ d₁ (Q r θ) * Qr r θ) (Frr := fun r θ ↦
        d₂ (Q r θ) * Qr r θ ^ 2 + d₁ (Q r θ) * Qrr r θ) (Ft := fun r θ ↦ d₁ (Q r θ) * (Ft r θ / J r)) (Ftt :=
        fun r θ ↦ d₂ (Q r θ) * (Ft r θ / J r) ^ 2 + d₁ (Q r θ) * (Ftt r θ / J r)) (w := W) (w' := W')
    · constructor
      all_goals
        try
          dsimp [d₁, d₂, smoothCap, smoothCapInputDeriv, smoothCapSecondDeriv]
          fun_prop (disch :=
            first
            | (intros; positivity)
            |
              (rintro p ⟨hp, _⟩;
                first
                | exact hp
                | have := hJpos hp; positivity))
      all_goals
        try
          intro r hr θ
          have hj := hJpos (Set.Ioo_subset_Ico_self hr)
          dsimp [Q, Qr, Qrr, d₁, d₂]
          differentiate
      · intro r hr
        simp [Q, F, Ft, P, polarIntegral, polarKernel, polarKernelT, polarDenominator, radialComponent,
          angularComponent]
    · apply ContinuousOn.mul ?_ (hJ.pow 2)
      apply ContinuousOn.rpow_const (by fun_prop)
      intro r hr
      exact Or.inl (sub_pos.mpr ((sq_lt_one_iff₀ hr.1).mpr hr.2)).ne'
    · intro r hr
      have ht := sub_pos.mpr (hr2 hr)
      have hj := (hJpos (Set.Ioo_subset_Ico_self hr)).ne'
      have hd := hJd r hr
      dsimp [W', W]
      eapply HasDerivAt.congr_deriv
      case h => fun_prop (disch := first | assumption | exact Or.inl ht.ne')
      rw [Real.rpow_sub_one ht.ne']
      field
    · intro r hr
      apply mul_pos (Real.rpow_pos_of_pos _ _) (sq_pos_of_pos (hJpos (Set.Ioo_subset_Ico_self hr)))
      exact sub_pos.mpr (hr2 hr)
    · intro r hr θ
      have hj := hJpos (Set.Ioo_subset_Ico_self hr)
      have ht := sub_pos.mpr (hr2 hr)
      have h : polarOperator k r (F r θ) (Fr r θ) (Frr r θ) (Ftt r θ) ≤ 0 :=
        by
        rw [polarIntegral_operator hK hμ hf.norm continuousOn_id
            (@hsource) _ q (hr2 hr) θ]
        apply integral_nonpos_of_ae
        filter_upwards [hμ] with w hw
        have hw' := hsource hw
        have hd := polarDenominator_pos (hr2 hr) hw' θ
        rw [polarKernel_equation k (id w) r θ hd hr.1.ne' ht.ne']
        simp [polarKernel, neg_div]
        positivity
      have h := div_nonpos_of_nonpos_of_nonneg h hj.le
      have hd₁ := smoothCapInputDeriv_nonneg (c := c) (x := Q r θ) ε
      have hr0 := hr.1
      have hsecond : d₂ (Q r θ) *
          (r * W r * Qr r θ ^ 2 + W r / r * (Ft r θ / J r) ^ 2) ≤ 0 := by
        dsimp [d₂, smoothCapSecondDeriv, W]
        simp only [neg_div, neg_mul, neg_nonpos]
        positivity
      convert add_nonpos (mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ r * W r * d₁ (Q r θ) by dsimp [W]; positivity) h) hsecond using 1
      dsimp [W', W, Qr, Qrr, polarOperator, Q]
      rw [eq_sub_of_add_eq (sub_eq_zero.mp (hJode r hr))]
      field  [hj.ne', hr.1.ne', ht.ne']
  · intro r hr
    dsimp only
    rw [Real.circleAverage_def, angularMean]
    simp only [weightedNormalizedPotential, norm_circleMap_zero, abs_of_nonneg hr.1, smul_eq_mul, P, polarIntegral]
    simp_rw [polarKernel_eq_norm_weightedKernel, weightedPotential]
    rfl


end BergmanWeakType.Weighted
