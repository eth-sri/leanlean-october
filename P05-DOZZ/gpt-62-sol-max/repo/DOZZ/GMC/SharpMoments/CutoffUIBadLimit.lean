/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffUIBad
public import DOZZ.GMC.SharpMoments.LimitWeightedFatou
public import DOZZ.GMC.SharpMoments.LimitExteriorFatou
public import DOZZ.GMC.SharpMoments.WeightedUniformGrid

/-! # The bad region of limiting Coulomb masses

The limiting Coulomb mass of the bad region also has a small moment, uniformly over compact
parameter sets. Near a root the Coulomb weight is the root singularity times a bounded factor, so
the root disks are weighted local masses, whose moments are bounded by the uniform cutoff weighted
bounds through Fatou's lemma; the far exterior is bounded by the far exterior cutoff moments in
the same way. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
include Ω X hX Xc hXc

/-- Limit moments of the bad part are uniformly small. -/
theorem cutoffUI_bad_limit_moment_le
    (Mfam : ℝ → Ω → Measure ℂ) (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ))
    (N : ℕ) (S : Set (CoulombParameters N)) (hS : IsCompact S) {tst : ℝ}
    (htst : 0 < tst)
    (hrootp : ∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, max (c.2.2.1 k) 0, tst))
    (hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst))
    {ρs : ℝ} (hρs : 0 < ρs) (hρs1 : ρs ≤ 1)
    (hsep : ∀ c ∈ S, ∀ j k, j ≠ k → 2 * ρs ≤ ‖c.2.1 j - c.2.1 k‖) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∃ A : ℝ≥0∞, A < ⊤ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ c ∈ S, ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ ρ1 →
        ∫⁻ ω, (∫⁻ x in coulombBadRegion c.2.1 ρ, coulombWeight c.1 c.2.2.1 c.2.1 c.2.2.2 x
          ∂Mfam c.1 ω) ^ tst ∂P ≤ A * ENNReal.ofReal (ρ ^ κ) := by
  classical
  have hadmInf : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 := fun c hc => by
    have h := (weightedCutoffSlack_pos_iff _).mp (hinf c hc)
    exact ⟨h.1, h.2.1⟩
  -- uniform sizes
  obtain ⟨Zs, E, hZs, hE, hZc, -, hEα, hEinf⟩ := compact_coulomb_bounds hS
  have hSα : ∀ c ∈ S, ∑ j, |c.1 * c.2.2.1 j| ≤ N * E := fun c hc => by
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hEα c hc j)
  obtain ⟨κr, hκr, Ck, -, hCkb⟩ := cutoffUI_root_moment_decay P X hX Xc hXc hS tst
    (fun k c => max (c.2.2.1 k) 0) (fun k => by fun_prop) hrootp hZc
  -- the far exterior
  set R0 : ℝ := 2 * Zs + 2 with hR0def
  have hR02 : 2 ≤ R0 := by linarith
  obtain ⟨Ae, hAe, κe, hκe, hfarb⟩ := cutoffUI_far_exterior_moment_le P X hX Xc hXc N S hS htst
    hinf hE hEinf hR02
  set κ : ℝ := min κr κe with hκdef
  let CRl : ℝ := ((2 + 2 * Zs) / ρs) ^ ((N + 1) * E)
  let CEl : ℝ := (2 : ℝ) ^ (N * E)
  let A := badRegionMomentCoeff tst (ENNReal.ofReal CRl) (ENNReal.ofReal CEl) (fun k => ENNReal.ofReal (Ck k)) Ae
  refine ⟨min ρs (1 / R0), lt_min hρs (by positivity), A,
    badRegionMomentCoeff_lt_top htst ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (fun _ => ENNReal.ofReal_lt_top) hAe, κ, lt_min hκr hκe, ?_⟩
  intro c hc ρ hρ hρ1
  obtain ⟨hγ0, hγ2⟩ := hadmInf c hc
  have hρs'  := hρ1.trans (min_le_left _ _)
  have hρR0  := hρ1.trans (min_le_right _ _)
  have hρ1'  := hρs'.trans hρs1
  have hinvρ : R0 ≤ 1 / ρ := by
    rw [le_div_iff₀ hρ]
    rw [le_div_iff₀ (by linarith)] at hρR0
    linarith
  set M : Ω → Measure ℂ := Mfam c.1 with hMdef
  have hM  := hMfam c.1 ⟨hγ0, hγ2⟩
  have hatoms  :=
    ae_all_iff.mpr fun k => gmc_singleton_mass_eq_zero_ae P X hX c.1 hγ0 hγ2 M hM (c.2.1 k)
  set W : Fin N → Ω → ℝ≥0∞ := fun k ω =>
    weightedGmcBallMass c.1 (M ω) (max (c.2.2.1 k) 0) (c.2.1 k) ρ with hW
  set V : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖},
    ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂M ω with hV
  -- constants are uniform
  have hS0 : 0 ≤ ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2| :=
    add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (abs_nonneg _)
  have hSE : ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2| ≤ (N + 1) * E := by
    linarith [hSα c hc, hEinf c hc]
  have hCRle : ENNReal.ofReal (((2 + 2 * ∑ j, ‖c.2.1 j‖) / ρs) ^
      (∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2|)) ≤ ENNReal.ofReal CRl := by
    refine ENNReal.ofReal_le_ofReal (real_rpow_le_rpow_of_le_of_le ?_ ?_ hS0 hSE)
    · rw [le_div_iff₀ hρs]
      linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => norm_nonneg (c.2.1 j))]
    · exact div_le_div_of_nonneg_right (by linarith [hZc c hc]) hρs.le
  have hCEle : ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |c.1 * c.2.2.1 j|)) ≤ ENNReal.ofReal CEl :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hSα c hc))
  have hzR : ∀ j, 2 * ‖c.2.1 j‖ ≤ 1 / ρ := fun j => by
    have := (Finset.single_le_sum (f := fun j => ‖c.2.1 j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ j)).trans (hZc c hc)
    linarith
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂P, (∫⁻ x in coulombBadRegion c.2.1 ρ,
      coulombWeight c.1 c.2.2.1 c.2.1 c.2.2.2 x ∂M ω) ≤
        ∑ k, ENNReal.ofReal CRl * W k ω + ENNReal.ofReal CEl * V ω := by
    filter_upwards [hatoms] with ω hω
    refine (lintegral_coulombBadRegion_le (M ω) _ c.2.1 ρ).trans
      (add_le_add (Finset.sum_le_sum fun k _ => ?_) ?_)
    · have hw : Measurable fun x : ℂ =>
          ENNReal.rpow (ENNReal.ofReal ‖x - c.2.1 k‖) (-c.1 * max (c.2.2.1 k) 0) :=
        (ENNReal.continuous_rpow_const (y := -c.1 * max (c.2.2.1 k) 0)).measurable.comp
          (ENNReal.measurable_ofReal.comp (measurable_id.sub_const _).norm)
      rw [hW]
      simp only []
      rw [weightedGmcBallMass, ← lintegral_const_mul _ hw]
      have hne' : ∀ᵐ x ∂(M ω).restrict (Metric.ball (c.2.1 k) ρ), x ≠ c.2.1 k :=
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (hω k))
      refine lintegral_mono_ae ?_
      filter_upwards [hne', ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hxk hx
      have hroot := coulombWeight_le_root c.1 c.2.2.1 c.2.1 c.2.2.2 k hρs hρs1
        (fun j hj => hsep c hc j k hj) (Metric.ball_subset_ball hρs' hx) hxk
      refine hroot.trans (mul_le_mul' hCRle ?_)
      have hxz : ENNReal.ofReal ‖x - c.2.1 k‖ ≤ 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hx
        exact ENNReal.ofReal_le_one.mpr (by linarith)
      refine ENNReal.rpow_le_rpow_of_exponent_ge hxz ?_
      have := mul_le_mul_of_nonneg_left (le_max_left (c.2.2.1 k) 0) hγ0.le
      linarith only [this]
    · refine lintegral_coulombExterior_le (M ω) _ _ (by fun_prop) _ _ fun x hx => ?_
      have hR : (1 : ℝ) ≤ 1 / ρ := (by linarith : 1 ≤ R0).trans hinvρ
      refine (coulombWeight_le_exterior c.1 c.2.2.1 c.2.1 c.2.2.2 hR hzR hx).trans
        (mul_le_mul' hCEle ?_)
      rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos (by linarith [hR.trans hx.le])]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hR.trans hx.le) (le_max_left _ _))
  have hWm : ∀ k, AEMeasurable (W k) P := fun k =>
    gmc_weighted_mass_aemeasurable P X hX c.1 hγ0 hγ2 M hM _ _ _
  have hVm : AEMeasurable V P :=
    gmc_setLIntegral_aemeasurable P X hX c.1 hγ0 hγ2 M hM _
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)) _
      (measurableSet_le measurable_const measurable_norm)
  refine badRegion_moment_le hWm hVm hpt htst (fun k => ?_) ?_
  · refine weightedGmcBallMoment_le_of_cutoff P X hX c.1 hγ0 hγ2 M hM Xc hXc
      (max (c.2.2.1 k) 0) (le_max_right _ _) (c.2.1 k) ρ hρ tst htst _ fun δ hδ hδρ => ?_
    exact (hCkb k c hc δ ρ hδ hδρ hρ1').trans (mul_le_mul' le_rfl
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hρ hρ1' (min_le_left _ _))))
  · refine (gmc_exterior_power_moment_le_of_cutoff P X hX c.1 hγ0 hγ2 M hM Xc hXc
      (R := 1 / ρ) (le_max_right (c.1 * c.2.2.2) 0) htst (Ae * ENNReal.ofReal (ρ ^ κe))
      (fun r hr => hfarb c hc ρ hρ hρR0 r hr)).trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1' (min_le_right _ _)

end

end DOZZ.Proofs
