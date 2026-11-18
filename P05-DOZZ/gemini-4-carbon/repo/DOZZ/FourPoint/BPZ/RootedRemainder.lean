/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.TaylorSingular
public import DOZZ.FourPoint.Fusion.FullTimeSplit
public import DOZZ.FourPoint.TaylorOneRootIdentity
public import DOZZ.FourPoint.TaylorRegionCover
public import DOZZ.FourPoint.TwoRootedDomination

/-! # The one- and two-rooted Taylor terms as a Taylor remainder

For `0 < t ≤ 1/4`, the sum `r₁ + r₂ + r₃ + p₁ + p₂ + p₃` of the one-rooted and two-rooted
Taylor terms at `z = t` is the Taylor remainder `∫ u in 0..t, (t - u) * g2 u` of any function
`g2` that on `(0, t]` is the corresponding six-term expression (`bpz_rootedTerms_eq_integral`). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

private lemma triple_integral {a b : ℝ → ℂ} {c₁ c₂ : ℝ}
    (ha : IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * a s) (Icc 0 1))
    (hb : IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * b s) (Icc 0 1)) :
    IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) *
      ((c₁ : ℂ) * a s + (c₂ : ℂ) * b s + star ((c₁ : ℂ) * a s))) (Icc 0 1) ∧
    (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) *
        ((c₁ : ℂ) * a s + (c₂ : ℂ) * b s + star ((c₁ : ℂ) * a s))) =
      (c₁ : ℂ) * (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * a s) +
        (c₂ : ℂ) * (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * b s) +
        star ((c₁ : ℂ) * ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * a s) := by
  have hA : Integrable (fun s : ℝ => (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s)) _ := ha.const_mul _
  have hB : Integrable (fun s : ℝ => (c₂ : ℂ) * (((1 - s : ℝ) : ℂ) * b s)) _ := hb.const_mul _
  have hAs : Integrable (fun s : ℝ => star ((c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s))) _ :=
    hA.norm.mono' (continuous_star.comp_aestronglyMeasurable hA.aestronglyMeasurable)
      (ae_of_all _ fun _ => by simp)
  have hpt (s : ℝ) : ((1 - s : ℝ) : ℂ) * ((c₁ : ℂ) * a s + (c₂ : ℂ) * b s + star ((c₁ : ℂ) * a s)) =
      (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s) + (c₂ : ℂ) * (((1 - s : ℝ) : ℂ) * b s) +
        star ((c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s)) := by
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]; ring
  have hAB : Integrable (fun s : ℝ => (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s) +
    (c₂ : ℂ) * (((1 - s : ℝ) : ℂ) * b s)) _ := hA.add hB
  refine ⟨(hAB.add hAs).congr (ae_of_all _ fun s => (hpt s).symm), ?_⟩
  simp_rw [hpt]
  rw [integral_add hAB hAs, integral_add hA hB]
  simp only [Complex.star_def, integral_conj, integral_const_mul]

/-- The one-rooted and two-rooted Taylor terms at a real point `t ∈ (0, 1/4]` add up to the
Taylor remainder `∫ u in 0..t, (t - u) * g2 u` of any function `g2` that on `(0, t]` equals the
six-term expression built from the four rooted expectations and their conjugates. -/
theorem bpz_rootedTerms_eq_integral (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁)
    (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {p : ℝ}
    (hp : 0 ≤ p) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 4) {g2 : ℝ → ℝ}
    (hpt : ∀ u : ℝ, 0 < u → u ≤ t →
      (g2 u : ℂ) =
        ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
            fusionPureSpatial P M γ α₁ α₂ α₃ p Set.univ (u : ℂ) +
          ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            fusionMixedSpatial P M γ α₁ α₂ α₃ p Set.univ (u : ℂ) +
          star (((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
            fusionPureSpatial P M γ α₁ α₂ α₃ p Set.univ (u : ℂ)) +
          ((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            (∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(u : ℂ), 0, 1] α₃)
              (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω (u : ℂ) ^ 2 ∂P) +
          ((2 * p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            (∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(u : ℂ), 0, 1] α₃)
              (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω (u : ℂ) *
                gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω (u : ℂ) ∂P) +
          star (((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            (∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(u : ℂ), 0, 1] α₃)
              (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω (u : ℂ) ^ 2 ∂P))) :
    gammaHalfOneRootedTerm P M γ α₁ α₂ α₃ p (t : ℂ) +
        gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p (t : ℂ) =
      ((∫ u in (0 : ℝ)..t, (t - u) * g2 u : ℝ) : ℂ) := by
  let _ := hX.1
  -- Two-rooted majorant bound
  have hk : 0 < γ ^ 2 / 2 := by positivity
  have hβ_lt : γ ^ 2 / 2 < γ * α₁ := by nlinarith
  have hβ2 : γ * α₁ < 2 := by linarith [(lt_div_iff₀ hγ).1 hα₁]
  set e := γ ^ 2 / 2 - γ * α₁
  have hexp_gt : -1 < e := by
    obtain ⟨-, -, -, hβe, -, -⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
    dsimp [e]; linarith
  have hmaj : ∃ C > 0, ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ 1 / 4 →
      gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p w ≤ ENNReal.ofReal (C * ‖w‖ ^ e) := by
    let Cr := Real.pi * (Real.Gamma (1 - γ * α₁ / 2) * Real.Gamma (γ ^ 2 / 2 / 2) *
      Real.Gamma ((γ * α₁ - γ ^ 2 / 2) / 2) / (Real.Gamma (γ * α₁ / 2) *
        Real.Gamma (1 - γ ^ 2 / 2 / 2) * Real.Gamma (1 + e / 2)))
    let C₁ := 2 ^ |γ * α₂| * |Cr| + 1
    have hC₁ : 0 < C₁ := by positivity
    obtain ⟨Ce, hCe, hext⟩ := twoRooted_exterior_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
    obtain ⟨C₀, hC₀, hsp⟩ := twoRooted_annular_spatial_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
    refine ⟨64 * (Ce + C₀ * C₁), by positivity, fun w hw hw4 => ?_⟩
    have hball : (∫⁻ x in Metric.ball (0 : ℂ) (1 / 2),
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ w x / ‖x - w‖ ^ 2)) ≤
        ENNReal.ofReal (C₁ * ‖w‖ ^ e) := by
      refine (lintegral_mono_ae ?_).trans ((setLIntegral_le_lintegral _
        (fun x => ENNReal.ofReal (2 ^ |γ * α₂| * planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w x))).trans ?_)
      · filter_upwards [ae_restrict_mem measurableSet_ball,
          ae_restrict_of_ae (Measure.ae_ne volume (0 : ℂ)),
          ae_restrict_of_ae (Measure.ae_ne volume w)] with x hx hx0 hxw
        exact ENNReal.ofReal_le_ofReal (fusion_localSecondKernel_bound γ α₁ α₂ α₃ w x
          (by simpa [Metric.mem_ball] using hx) hx0 hxw)
      · rw [← ofReal_integral_eq_lintegral_ofReal
            (((planar_mixed_integral _ _ hk hβ_lt hβ2 w hw).1).const_mul _)
            (ae_of_all _ fun _ => by unfold planarMixedKernel; positivity),
          integral_const_mul,
          (integral_congr_ae (g := fun u : ℂ => ‖u‖ ^ (-(γ * α₁)) * ‖u - w‖ ^ (γ ^ 2 / 2 - 2))
            (by
              filter_upwards [Measure.ae_ne volume (0 : ℂ)] with u _
              change ‖u - w‖ ^ (γ ^ 2 / 2 - 2) / ‖u‖ ^ (γ * α₁) = _
              rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg u), mul_comm])).trans
            (positive_riesz_convolution_integral (γ ^ 2 / 2) (γ * α₁) hk hβ_lt hβ2 w hw)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hN : 0 ≤ ‖w‖ ^ e := Real.rpow_nonneg (norm_nonneg _) _
        have : 2 ^ |γ * α₂| * Cr ≤ C₁ := by
          dsimp [C₁]; nlinarith [le_abs_self Cr, (by positivity : (0 : ℝ) ≤ 2 ^ |γ * α₂|)]
        nlinarith
    have hpow : 1 ≤ ‖w‖ ^ e := by
      rw [← Real.rpow_zero ‖w‖]
      exact Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.2 hw) (hw4.trans (by norm_num)) (by dsimp [e]; linarith)
    let Y := (Ce + C₀ * C₁) * ‖w‖ ^ e
    have h0 : gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w (Metric.ball 0 (1 / 2))ᶜ ≤ ENNReal.ofReal Y :=
      (hext w hw4).trans (ENNReal.ofReal_le_ofReal (by dsimp [Y]; nlinarith [mul_pos hC₀ hC₁]))
    have h1 : gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w (Metric.ball 0 (1 / 2)) ≤ ENNReal.ofReal Y :=
      (hsp w hw4 _ measurableSet_ball fun x hx => (by simpa [Metric.mem_ball] using hx : ‖x‖ < 1 / 2).le).trans
        ((mul_le_mul' le_rfl hball).trans (by
          rw [← ENNReal.ofReal_mul hC₀.le]
          exact ENNReal.ofReal_le_ofReal (by dsimp [Y]; nlinarith [Real.rpow_nonneg (norm_nonneg w) e])))
    refine (twoRooted_region_cover P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p w
      ![(Metric.ball (0 : ℂ) (1 / 2))ᶜ, Metric.ball 0 (1 / 2), Metric.ball 0 (1 / 2), Metric.ball 0 (1 / 2)]
      (fun i => by fin_cases i <;> [exact measurableSet_ball.compl; exact measurableSet_ball; exact measurableSet_ball; exact measurableSet_ball])
      (eq_univ_of_forall fun x => mem_iUnion.2 (by
        by_cases hx : x ∈ Metric.ball 0 (1 / 2) <;> [exact ⟨1, hx⟩; exact ⟨0, hx⟩]))).trans ?_
    refine (mul_le_mul' le_rfl (Finset.sum_le_sum (g := fun _ => ENNReal.ofReal Y)
      fun i _ => by fin_cases i <;> [exact h0; exact h1; exact h1; exact h1])).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      show (16 : ℝ≥0∞) * (4 : ℕ) = ENNReal.ofReal 64 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; dsimp [Y]; ring
  -- Measurability of two-rooted expectations
  obtain ⟨N, hN, hfN, heN⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have pair_meas {H₁ H₂ : ℂ × ℂ → ℂ} (hH₁ : Measurable H₁) (hH₂ : Measurable H₂) :
      Measurable fun w : ℂ => ∫ ω, ((ENNReal.rpow
        (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![w, 0, 1] α₃) (-p - 2)).toReal : ℂ) *
          (∫ x, H₁ (w, x) ∂M ω) * (∫ x, H₂ (w, x) ∂M ω) ∂P := by
    let I := fun q : ℂ × Ω => ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ q.1 x) ∂N q.2
    have hpr : Measurable fun q : (ℂ × Ω) × ℂ => (q.1.1, q.2) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have hIm : Measurable I := measurable_lintegral_finite_family (fun q : ℂ × Ω => N q.2)
      (hN.comp measurable_snd) (fun q => hfN q.2)
      (fun q : (ℂ × Ω) × ℂ => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ q.1.1 q.2))
      (by simpa only [Function.comp_def] using
        ENNReal.measurable_ofReal.comp ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp hpr))
    have hHm {H : ℂ × ℂ → ℂ} (hH : Measurable H) : Measurable fun q : ℂ × Ω => ∫ x, H (q.1, x) ∂N q.2 :=
      fusion_measurable_integral_finite_family (fun q : ℂ × Ω => N q.2) (hN.comp measurable_snd)
        (fun q => hfN q.2) (fun q : (ℂ × Ω) × ℂ => H (q.1.1, q.2))
        (by simpa only [Function.comp_def] using hH.comp hpr)
    have hFn : Measurable fun z : ℂ => ∫ ω, ((I (z, ω) ^ (-p - 2)).toReal : ℂ) *
        (∫ x, H₁ (z, x) ∂N ω) * (∫ x, H₂ (z, x) ∂N ω) ∂P :=
      ((((Complex.measurable_ofReal.comp (hIm.pow_const (-p - 2)).ennreal_toReal).mul
        (hHm hH₁)).mul (hHm hH₂)).stronglyMeasurable.integral_prod_right').measurable
    convert hFn using 1
    ext z; refine integral_congr_ae ?_
    filter_upwards [heN, gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hω hωz hω0 hω1
    dsimp only [I]
    rw [ENNReal.rpow_eq_pow, fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ z (M ω) hωz hω0 hω1, hω]
  -- Time integrability of the four expectations
  have hz0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
  have hz4 : ‖(t : ℂ)‖ ≤ 1 / 4 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0.le]
  obtain ⟨-, hβ, -, -, -, -⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
  obtain ⟨Cm, hCm, hIm⟩ := hmaj
  have hone_int (F : Set ℂ → ℂ → ℂ) (hm : ∀ S, MeasurableSet S → Measurable (F S)) {CL CE : ℝ}
      (hbL : ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ 1 / 4 → ‖F (Metric.ball 0 (1 / 2)) w‖ ≤ CL * ‖w‖ ^ e)
      (hbE : ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ 1 / 4 → ‖F (Metric.ball 0 (1 / 2))ᶜ w‖ ≤ CE)
      (hsp : ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ 1 / 4 → F univ w = F (Metric.ball 0 (1 / 2)) w + F (Metric.ball 0 (1 / 2))ᶜ w) :
      IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * F univ ((s : ℂ) * (t : ℂ))) (Icc 0 1) volume := by
    refine ((fusion_time_integrable_of_power_bound _ (hm _ measurableSet_ball) CL e (1 / 4) hexp_gt hbL _ hz0 hz4).add
      (fusion_time_integrable_of_power_bound _ (hm _ measurableSet_ball.compl) CE 0 (1 / 4) (by norm_num)
        (fun w hw hw4 => by rw [Real.rpow_zero, mul_one]; exact hbE w hw hw4) _ hz0 hz4)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with s hs hs0
    have hsz4 : ‖(s : ℂ) * (t : ℂ)‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans hz4
    show ((1 - s : ℝ) : ℂ) * F _ _ + ((1 - s : ℝ) : ℂ) * F _ _ = _
    rw [hsp _ (mul_ne_zero (Complex.ofReal_ne_zero.2 hs0) hz0) hsz4, mul_add]
  obtain ⟨_, _, hbL1⟩ := fusion_localR1_expectation_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp
  obtain ⟨_, _, hbE1⟩ := fusion_exteriorR1_expectation_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  obtain ⟨_, _, hbL2⟩ := fusion_localR2_expectation_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp
  obtain ⟨_, _, hbE2⟩ := fusion_exteriorR2_expectation_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  have i1 := hone_int (fusionPureSpatial P M γ α₁ α₂ α₃ p)
    (fusionPureSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p) hbL1 (fun w hw hw4 => (hbE1 w hw hw4).2)
    fun w hw hw4 => by simpa [fusionPureSpatial] using fusion_pureSpatial_expectation_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ p hp w hw hw4
  have i2 := hone_int (fusionMixedSpatial P M γ α₁ α₂ α₃ p)
    (fusionMixedSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p) hbL2 (fun w hw hw4 => (hbE2 w hw hw4).2)
    fun w hw hw4 => by simpa [fusionMixedSpatial] using fusion_mixedSpatial_expectation_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ p hp w hw hw4
  have hK := Complex.measurable_ofReal.comp (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃)
  have hHZ : Measurable fun q : ℂ × ℂ => (gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2 : ℂ) / (q.2 - q.1) :=
    hK.div (measurable_snd.sub measurable_fst)
  have hHBar : Measurable fun q : ℂ × ℂ => (gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2 : ℂ) / star (q.2 - q.1) :=
    hK.div (continuous_star.measurable.comp (measurable_snd.sub measurable_fst))
  let G₁ (w : ℂ) := ∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![w, 0, 1] α₃)
    (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω w ^ 2 ∂P
  let G₂ (w : ℂ) := ∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![w, 0, 1] α₃)
    (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω w *
      gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω w ∂P
  have htwo_int {G : ℂ → ℂ} (hGm : Measurable G)
      (hGe : ∀ w, ‖G w‖ₑ ≤ gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p w) :
      IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * G ((s : ℂ) * (t : ℂ))) (Icc 0 1) volume :=
    fusion_time_integrable_of_power_bound G hGm Cm e (1 / 4) hexp_gt
      (fun w hw hw4 => (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCm.le
        (Real.rpow_nonneg (norm_nonneg _) _))).1 (by rw [ofReal_norm]; exact (hGe w).trans (hIm w hw hw4)))
      (t : ℂ) hz0 hz4
  have i3 := htwo_int (G := G₁) (by simpa only [G₁, gammaHalfRootKernelZ, pow_two, mul_assoc] using pair_meas hHZ hHZ)
    fun w => by simpa only [G₁, ENNReal.rpow_eq_pow] using twoRooted_square_expectation_enorm_le P M γ α₁ α₂ α₃ p w
  have i4 := htwo_int (G := G₂) (by simpa only [G₂, gammaHalfRootKernelZ, gammaHalfRootKernelBar] using pair_meas hHZ hHBar)
    fun w => by simpa only [G₂, ENNReal.rpow_eq_pow] using twoRooted_mixed_expectation_enorm_le P M γ α₁ α₂ α₃ p w
  obtain ⟨ht1i, ht1⟩ := triple_integral (c₁ := -p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1))
    (c₂ := -2 * p * (γ ^ 2 / 4) ^ 2) i1 i2
  obtain ⟨ht2i, ht2⟩ := triple_integral (c₁ := p * (p + 1) * (γ ^ 2 / 4) ^ 2)
    (c₂ := 2 * p * (p + 1) * (γ ^ 2 / 4) ^ 2) i3 i4
  have h12 := (integral_add ht1i ht2i).trans (congrArg₂ (· + ·) ht1 ht2)
  have hae := (setIntegral_congr_ae (f := fun s : ℝ => ((1 - s : ℝ) : ℂ) * (g2 (s * t) : ℂ))
    measurableSet_Icc (by
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with s hs0 hs
      have h := hpt (s * t) (mul_pos (lt_of_le_of_ne hs.1 (Ne.symm hs0)) ht0) (mul_le_of_le_one_left ht0.le hs.2)
      rw [Complex.ofReal_mul s t] at h
      rw [h]; dsimp only [G₁, G₂]; ring)).trans h12
  have hrem : ((∫ u in (0 : ℝ)..t, (t - u) * g2 u : ℝ) : ℂ) =
      ((t ^ 2 : ℝ) : ℂ) * ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * (g2 (s * t) : ℂ) := by
    rw [← bpz_taylor_remainder_subst_complex (f := fun u => (g2 u : ℂ)) ht0, ← intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_mul]
  rw [hrem, hae]
  have hT2 : (t : ℂ) * star (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, sq]
  have hm (c I : ℂ) : c * (t : ℂ) * star (t : ℂ) * I = c * ((t ^ 2 : ℝ) : ℂ) * I := by
    rw [mul_assoc c, hT2]
  have hstar_cast (c T : ℝ) (I : ℂ) : star ((c : ℂ) * (T : ℂ) * I) = (T : ℂ) * star ((c : ℂ) * I) := by
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]; ring
  simp only [gammaHalfOneRootedTerm, gammaHalfTwoRootedTerm, gammaHalfRootedR3, gammaHalfTwoRootedP3,
    gammaHalfRootedR1, gammaHalfRootedR2, gammaHalfTwoRootedP1, gammaHalfTwoRootedP2,
    fusionPureSpatial, fusionMixedSpatial, Measure.restrict_univ, ENNReal.rpow_eq_pow,
    Complex.ofReal_pow, G₁, G₂]
  rw [hm, hm, (Complex.ofReal_pow t 2).symm, hstar_cast, hstar_cast]
  ring

end DOZZ.Proofs
