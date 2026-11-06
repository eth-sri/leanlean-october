module

public import RequestProject.ReconBasic
public import RequestProject.JordanWinding
public import RequestProject.ExteriorConnected
public import RequestProject.BoundaryConnected
public import RequestProject.ReconCauchy

/-!
# Green's formula on a Lipschitz Jordan domain

For a bounded simply connected Lipschitz domain `Ω` with positively oriented boundary
parametrization `γ` and a Lipschitz compactly supported `F : ℂ → ℂ`,

  `∫₀^{2π} F(γ(θ)) γ'(θ) dθ = 2i ∫_Ω ∂̄F`  (`integral_boundary_eq_dbar`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real ContDiff

noncomputable section

namespace PolyaNeumann

lemma norm_dbar_le   (hF : LipschitzWith K F) z :
    ‖dbar F z‖ ≤ K := by
  have hD := norm_fderiv_le_of_lipschitz ℝ hF (x₀ := z)
  have h1 : ‖fderiv ℝ F z 1‖ ≤ K :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by rw [norm_one, mul_one]; exact hD)
  have h2 : ‖fderiv ℝ F z Complex.I‖ ≤ K :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by rw [Complex.norm_I, mul_one]; exact hD)
  unfold dbar
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  have := norm_add_le (fderiv ℝ F z 1) (Complex.I * fderiv ℝ F z Complex.I)
  rw [norm_mul, Complex.norm_I, one_mul] at this
  linarith

lemma measurable_dbar F : Measurable (dbar F) := by
  unfold dbar
  exact ((measurable_fderiv_apply_const ℝ F 1).add
    (measurable_const.mul (measurable_fderiv_apply_const ℝ F Complex.I))).div_const 2

theorem integral_boundary_eq_dbar  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) 
    (hγ : IsBoundaryParam Ω γ)   (hF : LipschitzWith K F)
    (hFc : HasCompactSupport F) :
    ∫ θ in 0..(2 * π), F (γ θ) * deriv γ θ = 2 * Complex.I * ∫ z in Ω, dbar F z := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hΩo : IsOpen Ω := hL.1.1
  obtain ⟨σ, hσ, hin, hout⟩ :=
    windingNumber_pm_one_of_jordan hb hL hKγ hγ.periodic hγ.injOn hγ.image (by
      refine isConnected_compl_closure_of_frontier hb hL ?_
      rw [← hγ.image]
      exact isPreconnected_Icc.image γ hKγ.continuous.continuousOn)
  rw [show ∫ θ in 0..(2 * π), F (γ θ) * deriv γ θ = 2 * Complex.I * ∫ z, windingNumber γ z * dbar F z by
    have hpi : (0 : ℝ) ≤ 2 * π := by positivity
    obtain ⟨R₀, hR₀⟩ := hFc.isCompact.isBounded.subset_ball 0
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
      hKγ.continuous.continuousOn
    set R := max (max R₀ M) 1 with hR
    have hγR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ‖ ≤ R := fun θ hθ =>
      (hM θ hθ).trans ((le_max_right _ _).trans (le_max_left _ _))
    have hout : ∀ z, z ∉ ball 0 R → dbar F z = 0 := fun z hz =>
      have h_inl hz : dbar F z = 0 := by simp [dbar, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
      h_inl fun hs => hz (ball_subset_ball
        ((le_max_left _ _).trans (le_max_left _ _)) (hR₀ hs))
    set H : ℂ → ℝ → ℂ := fun z θ => dbar F z * (deriv γ θ * (γ θ - z)⁻¹) with hH
    have hHm : Measurable (Function.uncurry H) :=
      ((measurable_dbar F).comp measurable_fst).mul (((measurable_deriv γ).comp measurable_snd).mul
        ((hKγ.continuous.measurable.comp measurable_snd).sub measurable_fst).inv)
    rw [intervalIntegral.integral_of_le hpi, setIntegral_congr_fun measurableSet_Ioc (show ∀ θ ∈ Ioc 0 (2 * π), F (γ θ) * deriv γ θ = (π : ℂ)⁻¹ * ∫ z in ball 0 R, H z θ by
      intro θ hθ
      have h := integral_dbar_div_sub hF hFc (γ θ)
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball 0 R)
        (fun z hz => by rw [hout z hz, zero_div])] at h
      have e : ∫ z in ball 0 R, H z θ =
          -(∫ z in ball 0 R, dbar F z / (z - γ θ)) * deriv γ θ := by
        rw [neg_mul, ← integral_mul_const, ← integral_neg]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp [hH]
        rw [show γ θ - z = -(z - γ θ) by ring, inv_neg, div_eq_mul_inv]
        ring
      rw [e, h]
      field_simp),
      integral_const_mul, ← integral_integral_swap (by
        refine ⟨hHm.aestronglyMeasurable, ?_⟩
        rw [HasFiniteIntegral, lintegral_prod_symm _ hHm.enorm.aemeasurable]
        calc _
            ≤ _ :=
              setLIntegral_mono' measurableSet_Ioc (by
                intro θ hθ
                calc ∫⁻ z in ball 0 R, ‖Function.uncurry H (z, θ)‖ₑ
                    ≤ ∫⁻ z in ball 0 R, K * (Kγ * ‖γ θ - z‖ₑ⁻¹) := by
                      refine lintegral_mono fun z => ?_
                      simp [hH]
                      gcongr
                      · rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
                        exact ENNReal.ofReal_le_ofReal (norm_dbar_le hF z)
                      · rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
                        exact ENNReal.ofReal_le_ofReal (norm_deriv_le_of_lipschitzWith hKγ θ)
                      · exact enorm_inv_le_inv_enorm _
                  _ = _ := by
                      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
                        lintegral_const_mul' _ _ ENNReal.coe_ne_top]
                  _ ≤ K * (Kγ * ENNReal.ofReal (4 * π * R)) := by
                      gcongr
                      exact lintegral_ball_inv_norm_sub_le (le_trans zero_le_one (le_max_right _ _)) (hγR θ ⟨hθ.1.le, hθ.2⟩))
          _ < ⊤ := by
              rw [setLIntegral_const, Real.volume_Ioc]
              exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
                (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top)]
    have hin : ∀ z, ∫ θ in Ioc 0 (2 * π), H z θ =
        2 * π * Complex.I * (windingNumber γ z * dbar F z) := by
      intro z
      simp [hH]
      rw [integral_const_mul, windingNumber, intervalIntegral.integral_of_le hpi]
      simp only [div_eq_mul_inv]
      rw [← mul_assoc (2 * π * Complex.I), ← mul_assoc (2 * π * Complex.I),
        mul_inv_cancel₀ (by simp), one_mul]
      ring
    simp_rw [hin]
    rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by rw [hout z hz, mul_zero])]
    field_simp]
  congr 1
  rw [← integral_indicator hΩo.measurableSet]
  refine integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (show volume (frontier Ω) = 0 by
    rw [← hγ.image]; exact volume_image_Icc_eq_zero hKγ 0 (2 * π))] with z hz
  by_cases hzΩ : z ∈ Ω
  · rw [indicator_of_mem hzΩ, hin z hzΩ, show σ = 1 by
      have h := integral_signedAreaDensity_of_winding hΩo hb hKγ hγ.image σ hin hout
      have hV :=
        ENNReal.toReal_pos (hΩo.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
      have e : ∫ θ in 0..(2 * π), signedAreaDensity γ θ =
          ∫ θ in 0..(2 * π), (conj (γ θ) * deriv γ θ).im := rfl
      rw [e, hγ.area] at h
      rcases hσ with h1 | h1
      · exact h1
      · rw [h1] at h; nlinarith]; simp
  · rw [indicator_of_notMem hzΩ, hout z ?_, zero_mul]
    intro hc
    apply hz
    rw [frontier, hΩo.interior_eq]
    exact ⟨hc, hzΩ⟩

/-- Wirtinger decomposition of an `ℝ`-linear map: `L w = ∂L · w + ∂̄L · w̄`. -/
lemma clm_apply_wirtinger (L : ℂ →L[ℝ] ℂ) w :
    L w = (L 1 - Complex.I * L Complex.I) / 2 * w +
      (L 1 + Complex.I * L Complex.I) / 2 * conj w := by
  set a := w.re
  set b := w.im
  have hw : w = a + b * Complex.I := (Complex.re_add_im w).symm
  rw [show L w = a * L 1 + b * L Complex.I by
    have : w = a • 1 + b • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one]; exact hw
    rw [this, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul], show conj w = a - b * Complex.I by
    rw [hw]; simp; ring]
  conv_rhs => rw [hw]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma intervalIntegrable_comp_mul_deriv   (hK : LipschitzWith K γ)
    {G : ℂ → ℂ} (hG : Continuous G) :
    IntervalIntegrable (fun θ => G (γ θ) * deriv γ θ) volume 0 (2 * π) := by
  exact (show IntervalIntegrable (deriv γ) volume 0 (2 * π) by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr ?_
    exact Measure.integrableOn_of_bounded (M := K) measure_Ioc_lt_top.ne
      (measurable_deriv γ).aestronglyMeasurable
      (Eventually.of_forall fun θ => norm_deriv_le_of_lipschitz hK)).continuousOn_mul (hG.comp hK.continuous).continuousOn

/-- Green's identity for the double layer, for compactly supported `φ`. -/
theorem doubleLayer_eq_integral_of_hasCompactSupport {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) 
    (hγ : IsBoundaryParam Ω γ)   (hV : LipschitzWith K V)
    (hVc : HasCompactSupport V)  (hVh : ∀ θ ∈ Icc 0 (2 * π), V (γ θ) = h θ)
     (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    doubleLayer γ h φ =
      ∫ z in Ω, (V z * lap φ z + ∑ i : Fin 2, dirD V (coordDir i) z * dirD φ (coordDir i) z) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have h2π : 0 ≤ 2 * π := by positivity
  have hφt : TestFunction univ φ := ⟨hφ, hφc, subset_univ _⟩
  set p : ℂ → ℂ := fun z => 1 / 2 * dirD φ 1 z + (-Complex.I / 2) * dirD φ Complex.I z
    with hp
  set q : ℂ → ℂ := fun z => 1 / 2 * dirD φ 1 z + Complex.I / 2 * dirD φ Complex.I z
    with hq
  have hpt : TestFunction univ p := ((hφt.dirD 1).const_mul _).add ((hφt.dirD _).const_mul _)
  have hqt : TestFunction univ q := ((hφt.dirD 1).const_mul _).add ((hφt.dirD _).const_mul _)
  obtain ⟨Kp, hKp⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hpt.2.1 hpt.1 (by simp)
  obtain ⟨Kq, hKq⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hqt.2.1 hqt.1 (by simp)
  obtain ⟨Cp, hCp⟩ := hpt.2.1.exists_bound_of_continuous hpt.1.continuous
  obtain ⟨Cq, hCq⟩ := hqt.2.1.exists_bound_of_continuous hqt.1.continuous
  obtain ⟨CV, hCV⟩ := hVc.exists_bound_of_continuous hV.continuous
  obtain ⟨K1, hK1⟩ := lipschitzWith_mul_of_bounded hV hKp hCV hCp
  obtain ⟨K2', hK2'⟩ := lipschitzWith_mul_of_bounded hV hKq hCV hCq
  set F1 : ℂ → ℂ := fun z => V z * p z with hF1
  set F2 : ℂ → ℂ := fun z => conj (V z * q z) with hF2
  have hK2 : LipschitzWith (1 * K2') F2 := Complex.isometry_conj.lipschitz.comp hK2'
  have g1 := integral_boundary_eq_dbar hb hL hγ hK1 hVc.mul_right
  have g2 := integral_boundary_eq_dbar hb hL hγ hK2 ((hVc.mul_right (f' := q)).comp_left (g := conj) (map_zero _))
  -- the boundary side
  have hi2 := intervalIntegrable_comp_mul_deriv hKγ hK2.continuous
  rw [show doubleLayer γ h φ = -Complex.I * (∫ θ in 0..(2 * π), F1 (γ θ) * deriv γ θ) + Complex.I * conj (∫ θ in 0..(2 * π), F2 (γ θ) * deriv γ θ) by
    have hc : conj (∫ θ in 0..(2 * π), F2 (γ θ) * deriv γ θ) =
        ∫ θ in 0..(2 * π), conj (F2 (γ θ) * deriv γ θ) := by
      rw [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le h2π,
        integral_conj]
    rw [hc, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((intervalIntegrable_comp_mul_deriv hKγ hK1.continuous).const_mul _) ?_, doubleLayer]
    · refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le h2π] at hθ
      simp only [hF1, hF2, hp, hq, dirD]
      rw [← hVh θ hθ, clm_apply_wirtinger]
      simp only [map_mul, map_neg, Complex.conj_conj, Complex.conj_I]
      ring
    · have : IntervalIntegrable (fun θ => conj (F2 (γ θ) * deriv γ θ)) volume 0 (2 * π) := by
        rw [intervalIntegrable_iff] at hi2 ⊢
        exact (hi2.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
          hi2.aestronglyMeasurable) (Eventually.of_forall fun θ => by simp))
      exact this.const_mul _, g1, g2]
  -- the interior side
  have hdi : ∀ {F} {K}, LipschitzWith K F → IntegrableOn (dbar F) Ω := by
    intro F K hF
    exact Measure.integrableOn_of_bounded hb.measure_lt_top.ne (measurable_dbar F).aestronglyMeasurable
      (Eventually.of_forall (norm_dbar_le hF))
  have hc2 : IntegrableOn (fun z => conj (dbar F2 z)) Ω :=
    (hdi hK2).norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
      (hdi hK2).aestronglyMeasurable) (Eventually.of_forall fun z => by simp)
  have e : -Complex.I * (2 * Complex.I * ∫ z in Ω, dbar F1 z) +
      Complex.I * conj (2 * Complex.I * ∫ z in Ω, dbar F2 z) =
      ∫ z in Ω, 2 * dbar F1 z + 2 * conj (dbar F2 z) := by
    rw [integral_add ((hdi hK1).const_mul _) (hc2.const_mul _), integral_const_mul,
      integral_const_mul, map_mul, integral_conj.symm]
    simp only [map_mul, map_ofNat, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [e]
  refine setIntegral_congr_ae hL.1.1.measurableSet ?_
  filter_upwards [hV.ae_differentiableAt] with z hz _
  have hd1 : Differentiable ℝ (dirD φ 1) := (hφt.dirD 1).1.differentiable (by simp)
  have hdI : Differentiable ℝ (dirD φ Complex.I) := (hφt.dirD Complex.I).1.differentiable (by simp)
  have hqd : DifferentiableAt ℝ q z := hqt.1.differentiable (by simp) z
  have hf1 : fderiv ℝ F1 z = V z • fderiv ℝ p z + p z • fderiv ℝ V z := fderiv_fun_mul hz (hpt.1.differentiable (by simp) z)
  simp only [dbar, lap, hf1, show fderiv ℝ F2 z = Complex.conjCLE.toContinuousLinearMap.comp (V z • fderiv ℝ q z + q z • fderiv ℝ V z) by
    rw [← fderiv_fun_mul hz hqd]
    exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z (hz.mul hqd).hasFDerivAt).fderiv, show fderiv ℝ p z = (1 / 2 : ℂ) • fderiv ℝ (dirD φ 1) z + (-Complex.I / 2) • fderiv ℝ (dirD φ Complex.I) z by
    rw [hp, fderiv_fun_add ((hd1 z).const_mul _) ((hdI z).const_mul _), fderiv_const_mul (hd1 z),
      fderiv_const_mul (hdI z)], show fderiv ℝ q z = (1 / 2 : ℂ) • fderiv ℝ (dirD φ 1) z + (Complex.I / 2) • fderiv ℝ (dirD φ Complex.I) z by
    rw [hq, fderiv_fun_add ((hd1 z).const_mul _) ((hdI z).const_mul _), fderiv_const_mul (hd1 z),
      fderiv_const_mul (hdI z)], Fin.sum_univ_two]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, map_add, map_mul, map_neg, map_div₀, Complex.conj_conj, Complex.conj_I,
    map_ofNat, map_one, neg_neg,
    hp, hq, dirD, show coordDir 0 = 1 from rfl, show coordDir 1 = Complex.I from rfl]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Green's identity for the double layer: for `V` Lipschitz with compact support and trace
`h = V ∘ γ`, and `φ` smooth,
`μ_h(φ) = ∫_Ω (V Δφ + ∇V · ∇φ)`. -/
theorem doubleLayer_eq_integral  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) 
    (hγ : IsBoundaryParam Ω γ)   (hV : LipschitzWith K V)
    (hVc : HasCompactSupport V)  (hVh : ∀ θ ∈ Icc 0 (2 * π), V (γ θ) = h θ)
     (hφ : ContDiff ℝ ∞ φ) :
    doubleLayer γ h φ =
      ∫ z in Ω, (V z * lap φ z + ∑ i : Fin 2, dirD V (coordDir i) z * dirD φ (coordDir i) z) := by
  have hΩo : IsOpen Ω := hL.1.1
  obtain ⟨R₀, hR₀⟩ := hb.closure.subset_ball 0
  set R := max R₀ 1 with hR
  have hcl : closure Ω ⊆ ball 0 R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  set φ' : ℂ → ℂ := fun z => b z * φ z with hφ'
  have hφ'd : ContDiff ℝ (⊤ : ℕ∞) φ' :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).mul hφ
  have hφ'c : HasCompactSupport φ' :=
    (b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right
  have hD : ∀ z ∈ ball (0 : ℂ) R, fderiv ℝ φ' z = fderiv ℝ φ z := fun z hz =>
    ((show ∀ z ∈ ball (0 : ℂ) R, φ' =ᶠ[nhds z] φ by
      intro z hz
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      simp [hφ', b.one_of_mem_closedBall (ball_subset_closedBall hw)]) z hz).fderiv_eq
  have hDD : ∀ v w, ∀ z ∈ ball 0 R, dirD (dirD φ' v) w z = dirD (dirD φ v) w z :=
    fun v w z hz => by simp [dirD]; rw [((show ∀ v, ∀ z ∈ ball 0 R, dirD φ' v =ᶠ[nhds z] dirD φ v by
      intro v z hz
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      simp [dirD, hD w hw]) v z hz).fderiv_eq]
  have key := doubleLayer_eq_integral_of_hasCompactSupport hb hL hγ hV hVc hVh hφ'd hφ'c
  rw [← (show doubleLayer γ h φ' = doubleLayer γ h φ by
    unfold doubleLayer
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by positivity)] at hθ
    simp [hD _ (hcl (frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ hθ)))]), key]
  refine setIntegral_congr_fun hΩo.measurableSet fun z hz => ?_
  have hz' := hcl (subset_closure hz)
  simp [show lap φ' z = lap φ z by
    unfold lap; rw [hDD 1 1 z hz', hDD _ _ z hz'], dirD, hD z hz']

end PolyaNeumann
