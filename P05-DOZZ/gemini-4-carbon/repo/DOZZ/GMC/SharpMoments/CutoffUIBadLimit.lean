/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffUIBad
public import DOZZ.GMC.SharpMoments.LimitWeightedFatou
public import DOZZ.GMC.SharpMoments.LimitExteriorFatou
public import DOZZ.GMC.SharpMoments.WeightedUniformGrid

/-! # The bad region of limiting Coulomb masses -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs


/-- Limit moments of the bad part are uniformly small. -/
theorem cutoffUI_bad_limit_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Mfam : ℝ → Ω → Measure ℂ) (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ))
    (N : ℕ) (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S) {tst : ℝ}
    (htst : 0 < tst)
    (hrootp : ∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, max (c.2.2.1 k) 0, tst))
    (hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst))
    {ρs : ℝ} (hρs : 0 < ρs) (hρs1 : ρs ≤ 1)
    (hsep : ∀ c ∈ S, ∀ j k, j ≠ k → 2 * ρs ≤ ‖c.2.1 j - c.2.1 k‖) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∃ A : ℝ≥0∞, A < ⊤ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ c ∈ S, ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ ρ1 →
        ∫⁻ ω, (∫⁻ x in coulombBadRegion c.2.1 ρ, coulombWeight c.1 c.2.2.1 c.2.1 c.2.2.2 x
          ∂Mfam c.1 ω) ^ tst ∂P ≤ A * ENNReal.ofReal (ρ ^ κ) := by
  have far_ext_moment_le (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (N : ℕ) (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S) {tst : ℝ} (htst : 0 < tst) (hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst)) {E : ℝ} (hE : 0 ≤ E) (hEinf : ∀ c ∈ S, |c.1 * c.2.2.2| ≤ E) {R0 : ℝ} (hR0 : 2 ≤ R0) : ∃ A : ℝ≥0∞, A < ⊤ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ c ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / R0 →
        ∀ r : ℝ, 0 ≤ r →
          ∫⁻ ω, (∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0)
            ∂regularizedGMC P Xc c.1 r ω) ^ tst ∂P ≤ A * ENNReal.ofReal (ρ ^ κ) := by
    classical
    let _ := hX.1
    have hadm (c) (hc : c ∈ S) := (weightedCutoffSlack_pos_iff _).1 (hinf c hc)
    have hζi : ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ c ∈ S,
        κ ≤ 2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2 - max (c.1 * c.2.2.2) 0 * tst := by
      refine eventually_le_of_isCompact_of_pos hS (by fun_prop) fun c hc => ?_
      obtain ⟨hγ0, -, -, -, htinf⟩ := hadm c hc
      dsimp only at hγ0 htinf
      have h1 : c.1 * tst / 2 < Q c.1 - max c.2.2.2 0 := by
        have h := mul_lt_mul_of_pos_left (lt_min_iff.1 htinf).2 (half_pos hγ0)
        rw [show c.1 / 2 * (2 / c.1 * (Q c.1 - max c.2.2.2 0)) = Q c.1 - max c.2.2.2 0 by field_simp] at h
        linarith
      have hexp : 2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2 - max (c.1 * c.2.2.2) 0 * tst =
          c.1 * tst * ((Q c.1 - max c.2.2.2 0) - c.1 * tst / 2) := by
        have hmax : max (c.1 * c.2.2.2) 0 = c.1 * max c.2.2.2 0 := by
          rw [mul_max_of_nonneg _ _ hγ0.le, mul_zero]
        rw [hmax]
        have hQ : c.1 * Q c.1 = 2 + c.1 ^ 2 / 2 := by rw [Q]; field_simp
        linear_combination -tst * hQ
      rw [hexp]; exact mul_pos (mul_pos hγ0 htst) (by linarith)
    obtain ⟨κ, hκi, hκ0 : 0 < κ⟩ := (hζi.and self_mem_nhdsWithin).exists
    have hcont0 : ContinuousOn (fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => (c.1, (0 : ℝ), tst)) S :=
      continuous_fst.continuousOn.prodMk (continuousOn_const.prodMk continuousOn_const)
    obtain ⟨C0, hC0, hC0b⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
      (hS.image_of_continuousOn hcont0) (by
        rintro _ ⟨c, hc, rfl⟩
        obtain ⟨hγ0, hγ2, _, ht0, htm⟩ := hadm c hc
        dsimp only at hγ0 hγ2 ht0 htm
        refine (weightedCutoffSlack_pos_iff _).2 ⟨hγ0, hγ2, by rw [Q]; positivity, ht0,
          lt_min (lt_min_iff.1 htm).1 ((lt_min_iff.1 htm).1.trans ?_)⟩
        rw [sub_zero, Q]; field_simp; linarith [pow_pos hγ0 2])
      (closedBall 0 0) (isCompact_closedBall _ _) (2 * R0 + 1) (by linarith)
    let K0 := ENNReal.ofReal (C0 * (2 * R0 + 1) ^ (4 * tst))
    have hdisk (c) (hc : c ∈ S) (r : ℝ) (hr : 0 ≤ r) :
        ∫⁻ ω, regularizedGMC P Xc c.1 r ω (Metric.ball 0 (2 * R0 + 1)) ^ tst ∂P ≤ K0 := by
      obtain ⟨hγ0, hγ2, -⟩ := hadm c hc
      dsimp only at hγ0 hγ2
      have h := hC0b _ ⟨c, hc, rfl⟩ 0 (mem_closedBall_self le_rfl) (Real.exp (-r)) (2 * R0 + 1)
        (Real.exp_pos _) ((Real.exp_le_one_iff.2 (by linarith)).trans (by linarith)) le_rfl
      simp only [cutoffWeightedGmcBallMass_zero_charge] at h
      refine h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) hC0.le))
      have hQ : c.1 * Q c.1 = 2 + c.1 ^ 2 / 2 := by rw [Q]; field_simp
      have h1 := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hγ2 hγ0.le two_ne_zero) htst
      rw [sub_zero, hQ]; nlinarith
    let Gm := ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ κ) ^ (1 / max 1 tst)) ^ max 1 tst)⁻¹
    refine ⟨ENNReal.ofReal (2 ^ (E * tst) * R0 ^ (4 * tst)) * K0 * Gm,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (geometric_factor_lt_top hκ0), κ, hκ0, fun c hc ρ hρ hρR0 r hr => ?_⟩
    obtain ⟨hγ0, hγ2, -⟩ := hadm c hc
    dsimp only at hγ0 hγ2
    have hρ1 := hρR0.trans (by rw [div_le_one (by linarith)]; linarith)
    have hinvρ : R0 ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; rw [le_div_iff₀ (by linarith)] at hρR0; linarith
    have hK0b (r' : ℝ) (hr' : 0 ≤ r') :
        ∫⁻ ω, regularizedGMC P Xc c.1 r' ω (exteriorAnnulus R0 0) ^ tst ∂P ≤ K0 :=
      (lintegral_mono fun ω => ENNReal.rpow_le_rpow (measure_mono fun x hx => by
        rw [Metric.mem_ball, dist_zero_right]; have := hx.2; simp at this; linarith) htst.le).trans
        (hdisk c hc r' hr')
    have hext := cutoff_exterior_power_moment_le P X hX Xc hXc c.1 (hR0.trans hinvρ)
      (le_max_right (c.1 * c.2.2.2) 0) htst
      (fun r' hr' => exteriorAnnulus_moment_le_far P X hX Xc hXc c.1 hR0 hinvρ hK0b hr') hr
    refine hext.trans ?_
    have hξ : 2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2 ≤ 4 * tst := by
      nlinarith [mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hγ2 hγ0.le two_ne_zero) htst]
    have hc1 := farExterior_coeff_le (κ := κ) (R0 := R0) hρ hρ1 (by linarith)
      (max_le ((le_abs_self _).trans (hEinf c hc)) hE) htst hξ (by linarith [hκi c hc])
    have hc2 := geometric_factor_le hκ0 (hκi c hc) (le_refl tst)
    rw [← mul_assoc (ENNReal.ofReal _), ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    refine (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hc1) le_rfl) hc2).trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity)]; ring
  classical
  let _ := hX.1
  have hadmInf (c) (hc : c ∈ S) : 0 < c.1 ∧ c.1 < 2 := by
    have h := (weightedCutoffSlack_pos_iff _).1 (hinf c hc); exact ⟨h.1, h.2.1⟩
  obtain ⟨Zs0, hZs0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => ∑ j, ‖c.2.1 j‖) (by fun_prop)
  obtain ⟨E0, hE0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2|) (by fun_prop)
  let Zs := max Zs0 0
  let E := max E0 0
  have hZs : 0 ≤ Zs := le_max_right _ _
  have hE : 0 ≤ E := le_max_right _ _
  have hZc (c) (hc : c ∈ S) : ∑ j, ‖c.2.1 j‖ ≤ Zs := by
    have h := hZs0 c hc
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  have hEsum (c) (hc : c ∈ S) : ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2| ≤ E := by
    have h := hE0 c hc
    rw [Real.norm_of_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _))] at h
    exact h.trans (le_max_left _ _)
  have hEinf (c) (hc : c ∈ S) : |c.1 * c.2.2.2| ≤ E := by
    linarith [hEsum c hc, Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => abs_nonneg (c.1 * c.2.2.1 j)]
  have hSα (c) (hc : c ∈ S) : ∑ j, |c.1 * c.2.2.1 j| ≤ N * E := by
    refine (Finset.sum_le_sum (g := fun _ : Fin N => E) fun j _ => ?_).trans_eq (by simp)
    linarith [hEsum c hc, abs_nonneg (c.1 * c.2.2.2),
      Finset.single_le_sum (f := fun j => |c.1 * c.2.2.1 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)]
  have hζr (k : Fin N) : ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ c ∈ S,
      κ ≤ c.1 * (Q c.1 - max (c.2.2.1 k) 0) * tst - c.1 ^ 2 * tst ^ 2 / 2 := by
    refine eventually_le_of_isCompact_of_pos hS (fun c hc => ?_) fun c hc => ?_
    · have h := (hadmInf c hc).1.ne'
      exact (by simp only [Q]; fun_prop (disch := first | exact h | exact pow_ne_zero _ h) :
        ContinuousAt _ c).continuousWithinAt
    · obtain ⟨hγ0, -, -, -, ht⟩ := (weightedCutoffSlack_pos_iff _).1 (hrootp c hc k)
      dsimp only at hγ0 ht
      have h1 : c.1 * tst / 2 < Q c.1 - max (c.2.2.1 k) 0 := by
        have h := mul_lt_mul_of_pos_left (lt_min_iff.1 ht).2 (half_pos hγ0)
        rw [show c.1 / 2 * (2 / c.1 * (Q c.1 - max (c.2.2.1 k) 0)) = Q c.1 - max (c.2.2.1 k) 0 by field_simp] at h
        linarith
      rw [show c.1 * (Q c.1 - max (c.2.2.1 k) 0) * tst - c.1 ^ 2 * tst ^ 2 / 2 =
        c.1 * tst * ((Q c.1 - max (c.2.2.1 k) 0) - c.1 * tst / 2) by ring]
      exact mul_pos (mul_pos hγ0 htst) (by linarith)
  obtain ⟨κr, hκr, hκr0 : 0 < κr⟩ := ((eventually_all.2 hζr).and self_mem_nhdsWithin).exists
  let R0 := 2 * Zs + 2
  obtain ⟨Ae, hAe, κe, hκe, hfarb⟩ := far_ext_moment_le (R0 := R0) P X hX Xc hXc N S hS htst hinf hE hEinf (by dsimp [R0]; linarith)
  let κ := min κr κe
  have hCk (k : Fin N) : ∃ C : ℝ, 0 < C ∧ ∀ c ∈ S, ∀ δ R : ℝ, 0 < δ → δ ≤ R → R ≤ 1 →
      (∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc c.1 (max (c.2.2.1 k) 0) (c.2.1 k) R δ ω) tst ∂P) ≤
        ENNReal.ofReal (C * Real.rpow R (c.1 * (Q c.1 - max (c.2.2.1 k) 0) * tst - c.1 ^ 2 * tst ^ 2 / 2)) := by
    have hcont : ContinuousOn (fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => (c.1, max (c.2.2.1 k) 0, tst)) S :=
      continuous_fst.continuousOn.prodMk ((((continuous_apply k).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))).max continuous_const).continuousOn.prodMk continuousOn_const)
    obtain ⟨C, hC, hCb⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
      (hS.image_of_continuousOn hcont) (by rintro _ ⟨c, hc, rfl⟩; exact hrootp c hc k)
      (closedBall 0 Zs) (isCompact_closedBall _ _) 1 one_pos
    refine ⟨C, hC, fun c hc δ R hδ hδR hR1 => hCb _ ⟨c, hc, rfl⟩ _ ?_ δ R hδ hδR hR1⟩
    rw [mem_closedBall, dist_zero_right]
    exact (Finset.single_le_sum (f := fun j => ‖c.2.1 j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans (hZc c hc)
  choose Ck hCkpos hCkb using hCk
  let CRl := ((2 + 2 * Zs) / ρs) ^ ((N + 1) * E)
  let CEl := (2 : ℝ) ^ (N * E)
  let A : ℝ≥0∞ := 2 ^ tst * (2 ^ tst * ((N : ℝ≥0∞) ^ tst *
    ∑ k, ENNReal.ofReal CRl ^ tst * ENNReal.ofReal (Ck k)) + ENNReal.ofReal CEl ^ tst * Ae)
  have hfin {x : ℝ≥0∞} (hx : x ≠ ⊤) : x ^ tst < ⊤ := ENNReal.rpow_lt_top_of_nonneg htst.le hx
  refine ⟨min ρs (1 / R0), lt_min hρs (by dsimp [R0]; positivity), A,
    ENNReal.mul_lt_top (hfin (by norm_num)) (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top (hfin (by norm_num)) (ENNReal.mul_lt_top (hfin (ENNReal.natCast_ne_top N))
        (ENNReal.sum_lt_top.2 fun k _ => ENNReal.mul_lt_top (hfin ENNReal.ofReal_ne_top) ENNReal.ofReal_lt_top)),
       ENNReal.mul_lt_top (hfin ENNReal.ofReal_ne_top) hAe⟩),
    κ, lt_min hκr0 hκe, fun c hc ρ hρ hρ1 => ?_⟩
  obtain ⟨hγ0, hγ2⟩ := hadmInf c hc
  have hρs' := hρ1.trans (min_le_left _ _)
  have hρR0 := hρ1.trans (min_le_right _ _)
  have hρ1' := hρs'.trans hρs1
  have hinvρ : R0 ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; rw [le_div_iff₀ (by dsimp [R0]; positivity)] at hρR0; linarith
  let M := Mfam c.1
  have hM : IsGMCOf P X c.1 M := hMfam c.1 ⟨hγ0, hγ2⟩
  let W (k : Fin N) (ω : Ω) := weightedGmcBallMass c.1 (M ω) (max (c.2.2.1 k) 0) (c.2.1 k) ρ
  let V (ω : Ω) := ∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂M ω
  have hCRle : ENNReal.ofReal (((2 + 2 * ∑ j, ‖c.2.1 j‖) / ρs) ^
      (∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2|)) ≤ ENNReal.ofReal CRl :=
    ENNReal.ofReal_le_ofReal (real_rpow_le_rpow_of_le_of_le
      ((le_div_iff₀ hρs).2 (by linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => norm_nonneg (c.2.1 j)]))
      (div_le_div_of_nonneg_right (by linarith [hZc c hc]) hρs.le)
      (add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _))
      (by linarith [hSα c hc, hEinf c hc]))
  have hCEle : ENNReal.ofReal ((2 : ℝ) ^ ∑ j, |c.1 * c.2.2.1 j|) ≤ ENNReal.ofReal CEl :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le one_le_two (hSα c hc))
  have hzR (j : Fin N) : 2 * ‖c.2.1 j‖ ≤ 1 / ρ := by
    have := (Finset.single_le_sum (f := fun j => ‖c.2.1 j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans (hZc c hc)
    dsimp [R0] at hinvρ; linarith
  have hpt : ∀ᵐ ω ∂P, (∫⁻ x in coulombBadRegion c.2.1 ρ, coulombWeight c.1 c.2.2.1 c.2.1 c.2.2.2 x ∂M ω) ≤
      ∑ k, ENNReal.ofReal CRl * W k ω + 0 * 0 + ENNReal.ofReal CEl * V ω := by
    filter_upwards [ae_all_iff.2 fun k => gmc_singleton_mass_eq_zero_ae P X hX c.1 hγ0 hγ2 M hM (c.2.1 k)] with ω hω
    refine (lintegral_coulombBadRegion_le (M ω) _ (measurable_coulombWeight _ _ _ _) c.2.1 ρ).trans ?_
    rw [mul_zero, add_zero]
    refine add_le_add (Finset.sum_le_sum fun k _ => ?_) ?_
    · have hw : Measurable fun x : ℂ => ENNReal.rpow (ENNReal.ofReal ‖x - c.2.1 k‖) (-c.1 * max (c.2.2.1 k) 0) :=
        (ENNReal.continuous_rpow_const (y := -c.1 * max (c.2.2.1 k) 0)).measurable.comp
          (ENNReal.measurable_ofReal.comp (measurable_id.sub_const _).norm)
      dsimp only [W]; rw [weightedGmcBallMass, ← lintegral_const_mul _ hw]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hω k)),
        ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hxk hx
      refine (coulombWeight_le_root c.1 c.2.2.1 c.2.1 c.2.2.2 k hρs hρs1 (fun j hj => hsep c hc j k hj)
        (Metric.ball_subset_ball hρs' hx) hxk).trans (mul_le_mul' hCRle ?_)
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.2 (by linarith))
        (by linarith [mul_le_mul_of_nonneg_left (le_max_left (c.2.2.1 k) 0) hγ0.le])
    · have hpow : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) :=
        ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
      dsimp only [V]; rw [← lintegral_const_mul _ hpow]
      refine (setLIntegral_mono' (measurableSet_lt measurable_const measurable_norm) fun x (hx : 1 / ρ < ‖x‖) => ?_).trans
        (lintegral_mono_set fun _ (hx : 1 / ρ < _) => hx.le)
      have hx1 : 1 ≤ ‖x‖ := by dsimp [R0] at hinvρ; linarith
      refine (coulombWeight_le_exterior c.1 c.2.2.1 c.2.1 c.2.2.2 (by dsimp [R0] at hinvρ; linarith) hzR hx).trans
        (mul_le_mul' hCEle ?_)
      rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos (by linarith)]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _))
  have hmom := lintegral_rpow_le_of_le_pieces _ W (fun _ => 0) V (fun _ => ENNReal.ofReal CRl) 0
    (ENNReal.ofReal CEl) (fun k => gmc_weighted_mass_aemeasurable P X hX c.1 hγ0 hγ2 M hM _ _ _)
    aemeasurable_const (gmc_setLIntegral_aemeasurable P X hX c.1 hγ0 hγ2 M hM _
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)) _
      (measurableSet_le measurable_const measurable_norm)) hpt htst
  refine hmom.trans ?_
  have hWb (k : Fin N) : ∫⁻ ω, W k ω ^ tst ∂P ≤ ENNReal.ofReal (Ck k) * ENNReal.ofReal (ρ ^ κ) :=
    weightedGmcBallMoment_le_of_cutoff P X hX c.1 hγ0 hγ2 M hM Xc hXc
      (max (c.2.2.1 k) 0) (le_max_right _ _) (c.2.1 k) ρ hρ tst htst _ fun δ hδ hδρ =>
        (hCkb k c hc δ ρ hδ hδρ hρ1').trans (by
          rw [← ENNReal.ofReal_mul (hCkpos k).le]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hρ hρ1' ((min_le_left _ _).trans (hκr k c hc))) (hCkpos k).le))
  have hVb : ∫⁻ ω, V ω ^ tst ∂P ≤ Ae * ENNReal.ofReal (ρ ^ κ) :=
    (gmc_exterior_power_moment_le_of_cutoff P X hX c.1 hγ0 hγ2 M hM Xc hXc
      (R := 1 / ρ) (le_max_right (c.1 * c.2.2.2) 0) htst (Ae * ENNReal.ofReal (ρ ^ κe))
      fun r hr => hfarb c hc ρ hρ hρR0 r hr).trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hρ hρ1' (min_le_right _ _))))
  simp only [ENNReal.zero_rpow_of_pos htst, zero_mul, add_zero]
  calc 2 ^ tst * (2 ^ tst * ((N : ℝ≥0∞) ^ tst * ∑ k, ENNReal.ofReal CRl ^ tst * ∫⁻ ω, W k ω ^ tst ∂P) +
        ENNReal.ofReal CEl ^ tst * ∫⁻ ω, V ω ^ tst ∂P)
    _ ≤ 2 ^ tst * (2 ^ tst * ((N : ℝ≥0∞) ^ tst *
        ∑ k, ENNReal.ofReal CRl ^ tst * (ENNReal.ofReal (Ck k) * ENNReal.ofReal (ρ ^ κ))) +
        ENNReal.ofReal CEl ^ tst * (Ae * ENNReal.ofReal (ρ ^ κ))) := by gcongr with k; exact hWb k
    _ = A * ENNReal.ofReal (ρ ^ κ) := by
        dsimp [A]
        rw [show (∑ k, ENNReal.ofReal CRl ^ tst * (ENNReal.ofReal (Ck k) * ENNReal.ofReal (ρ ^ κ))) =
          (∑ k, ENNReal.ofReal CRl ^ tst * ENNReal.ofReal (Ck k)) * ENNReal.ofReal (ρ ^ κ) by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring]
        ring

end DOZZ.Proofs
