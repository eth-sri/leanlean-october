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
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {F : ℂ → ℂ} {γ : ℝ → ℂ} {K : NNReal} {Ω : Set ℂ}

lemma norm_dbar_le (hF : LipschitzWith K F) (z : ℂ) :
    ‖dbar F z‖ ≤ K := by
  have hD := norm_fderiv_le_of_lipschitz ℝ hF (x₀ := z)
  have h1 : ‖fderiv ℝ F z 1‖ ≤ K :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by simp_all)
  have h2 : ‖fderiv ℝ F z Complex.I‖ ≤ K :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by simp_all)
  unfold dbar
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  have := norm_add_le (fderiv ℝ F z 1) (Complex.I * fderiv ℝ F z Complex.I)
  rw [norm_mul, Complex.norm_I] at this
  linarith

lemma measurable_dbar (F : ℂ → ℂ) : Measurable (dbar F) := ((measurable_fderiv_apply_const ℝ F 1).add
    (measurable_const.mul (measurable_fderiv_apply_const ℝ F Complex.I))).div_const 2

lemma dbar_eq_zero_of_notMem {z : ℂ} (hz : z ∉ tsupport F) : dbar F z = 0 := by
  simp [dbar, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]

/-- Green's formula through winding numbers:
`∫₀^{2π} F(γ) γ' = 2i ∫_ℂ wind(γ, z) ∂̄F(z) dz`. -/
theorem integral_comp_mul_deriv_eq_wind {Kγ : NNReal} (hγ : LipschitzWith Kγ γ)
    {F : ℂ → ℂ} {K : NNReal} (hF : LipschitzWith K F) (hFc : HasCompactSupport F) :
    ∫ θ in 0..(2 * π), F (γ θ) * deriv γ θ =
      2 * Complex.I * ∫ z, windingNumber γ z * dbar F z := by
  have hpi : 0 ≤ 2 * π := by positivity
  obtain ⟨R₀, hR₀⟩ := hFc.isCompact.isBounded.subset_ball 0
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn 
    hγ.continuous.continuousOn
  set R := max (max R₀ M) 1 with hR
  have hout : ∀ z, z ∉ ball 0 R → dbar F z = 0 := fun z hz =>
    dbar_eq_zero_of_notMem fun hs => hz (ball_subset_ball
      ((le_max_left _ _).trans (le_max_left _ _)) (hR₀ hs))
  set H : ℂ → ℝ → ℂ := fun z θ => dbar F z * (deriv γ θ * (γ θ - z)⁻¹) with hH
  have hHm : Measurable (Function.uncurry H) :=
    ((measurable_dbar F).comp measurable_fst).mul (((measurable_deriv γ).comp measurable_snd).mul
      ((hγ.continuous.measurable.comp measurable_snd).sub measurable_fst).inv)
  have hCP : ∀ θ ∈ Ioc 0 (2 * π), F (γ θ) * deriv γ θ =
      (π : ℂ)⁻¹ * ∫ z in ball 0 R, H z θ := by
    intro θ hθ
    have h := integral_dbar_div_sub hF hFc (γ θ)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero 
      (fun z hz => by rw [hout z hz, zero_div])] at h
    have e : ∫ z in ball 0 R, H z θ =
        -(∫ z in ball 0 R, dbar F z / (z - γ θ)) * deriv γ θ := by
      rw [neg_mul, ← integral_mul_const, ← integral_neg]
      grind
    rw [e, h]
    field_simp
  rw [intervalIntegral.integral_of_le hpi, setIntegral_congr_fun measurableSet_Ioc hCP,
    integral_const_mul, ← integral_integral_swap (by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod_symm _ hHm.enorm.aemeasurable]
    calc ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ z in ball 0 R, ‖Function.uncurry H (z, θ)‖ₑ
        ≤ ∫⁻ θ in Ioc 0 (2 * π), K * (Kγ * ENNReal.ofReal (4 * π * R)) :=
          setLIntegral_mono' measurableSet_Ioc (by
      intro θ hθ
      calc ∫⁻ z in ball 0 R, ‖Function.uncurry H (z, θ)‖ₑ
          ≤ ∫⁻ z in ball 0 R, K * (Kγ * ‖γ θ - z‖ₑ⁻¹) := by
            simp only [Function.uncurry_apply_pair, hH, enorm_mul]
            gcongr
            · rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
              exact ENNReal.ofReal_le_ofReal (norm_dbar_le hF z)
            · rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
              exact ENNReal.ofReal_le_ofReal (norm_deriv_le_of_lipschitzWith hγ θ)
            · exact enorm_inv_le_inv_enorm _
        _ = K * (Kγ * ∫⁻ z in ball 0 R, ‖γ θ - z‖ₑ⁻¹) := by
            simp [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        _ ≤ K * (Kγ * ENNReal.ofReal (4 * π * R)) := by
            gcongr
            exact lintegral_ball_inv_norm_sub_le (le_trans zero_le_one (le_max_right _ _)) ((fun θ hθ =>
    (hM θ hθ).trans ((le_max_right _ _).trans (le_max_left _ _))) θ ⟨hθ.1.le, hθ.2⟩))
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioc]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
            (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top)]
  have hin : ∀ z, ∫ θ in Ioc 0 (2 * π), H z θ =
      (2 * π * Complex.I) * (windingNumber γ z * dbar F z) := by
    intro z
    rw [integral_const_mul, windingNumber, intervalIntegral.integral_of_le hpi]
    field_simp
  simp_rw [hin]
  rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => by simp_all)]
  field_simp

/-- Complex Green formula `∮_{∂Ω} F dz = 2i ∫_Ω ∂̄F` for Lipschitz compactly supported `F`. -/
theorem integral_boundary_eq_dbar (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {F : ℂ → ℂ} {K : NNReal} (hF : LipschitzWith K F)
    (hFc : HasCompactSupport F) :
    ∫ θ in 0..(2 * π), F (γ θ) * deriv γ θ = 2 * Complex.I * ∫ z in Ω, dbar F z := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hΩo  := hL.1.1
  obtain ⟨σ, hσ, hin, hout⟩ :=
    windingNumber_pm_one_of_jordan hb hL hKγ hγ.periodic hγ.injOn hγ.image (by
    refine isConnected_compl_closure_of_frontier hb hL ?_
    rw [← hγ.image]
    exact isPreconnected_Icc.image γ hKγ.continuous.continuousOn)
  have hσ1 : σ = 1 := by
    have h := integral_signedAreaDensity_of_winding hΩo hb hKγ hγ.image σ hin hout
    have harea := hγ.area
    have hV  :=
      ENNReal.toReal_pos (hΩo.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
    have e : ∫ θ in 0..(2 * π), signedAreaDensity γ θ =
        ∫ θ in 0..(2 * π), (conj (γ θ) * deriv γ θ).im := rfl
    grind
  rw [integral_comp_mul_deriv_eq_wind hKγ hF hFc]
  congr 1
  rw [← integral_indicator hΩo.measurableSet]
  refine integral_congr_ae ?_
  have h0 : volume (frontier Ω) = 0 := by
    rw [← hγ.image]; exact volume_image_Icc_eq_zero hKγ 0 (2 * π)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with z hz
  by_cases hzΩ : z ∈ Ω
  · simp_all
  simp_all [frontier, hΩo.interior_eq]

/-- Wirtinger decomposition of an `ℝ`-linear map: `L w = ∂L · w + ∂̄L · w̄`. -/
lemma clm_apply_wirtinger (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = (L 1 - Complex.I * L Complex.I) / 2 * w +
      (L 1 + Complex.I * L Complex.I) / 2 * conj w := by
  set a := w.re
  set b := w.im
  have hw : w = a + b * Complex.I := (Complex.re_add_im w).symm
  have hconj : conj w = a - b * Complex.I := by
    rw [hw]; simp ; ring
  have hL : L w = a * L 1 + b * L Complex.I := by
    have : w = a • 1 + b • Complex.I := by
      simp_all
    rw [this, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [hL, hconj]
  conv_rhs => rw [hw]
  ring_nf
  norm_num

lemma intervalIntegrable_comp_mul_deriv (hK : LipschitzWith K γ)
    {G : ℂ → ℂ} (hG : Continuous G) :
    IntervalIntegrable (fun θ => G (γ θ) * deriv γ θ) volume 0 (2 * π) := by
  have hd : IntervalIntegrable (deriv γ) volume 0 (2 * π) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr ?_
    exact Measure.integrableOn_of_bounded  measure_Ioc_lt_top.ne
      (measurable_deriv γ).aestronglyMeasurable
      (Eventually.of_forall fun θ => norm_deriv_le_of_lipschitz hK)
  exact hd.continuousOn_mul (hG.comp hK.continuous).continuousOn

/-- Green's identity for the double layer, for compactly supported `φ`. -/
theorem doubleLayer_eq_integral_of_hasCompactSupport {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {V : ℂ → ℂ} {K : NNReal} (hV : LipschitzWith K V)
    (hVc : HasCompactSupport V) {h : ℝ → ℂ} (hVh : ∀ θ ∈ Icc 0 (2 * π), V (γ θ) = h θ)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    doubleLayer γ h φ =
      ∫ z in Ω, (V z * lap φ z + ∑ i : Fin 2, dirD V (coordDir i) z * dirD φ (coordDir i) z) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hΩo  := hL.1.1
  have h2π : 0 ≤ 2 * π := by positivity
  have hφt : TestFunction univ φ := ⟨hφ, hφc, subset_univ _⟩
  set p : ℂ → ℂ := fun z => 1 / 2 * dirD φ 1 z + (-Complex.I / 2) * dirD φ Complex.I z
    with hp
  set q : ℂ → ℂ := fun z => 1 / 2 * dirD φ 1 z + (Complex.I / 2) * dirD φ Complex.I z
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
  have hF2c : HasCompactSupport F2 :=
    (hVc.mul_right ).comp_left  (map_zero _)
  have g1 := integral_boundary_eq_dbar hb hL hγ hK1 hVc.mul_right
  have hi2 := intervalIntegrable_comp_mul_deriv hKγ hK2.continuous
  have hdl : doubleLayer γ h φ = -Complex.I * (∫ θ in 0..(2 * π), F1 (γ θ) * deriv γ θ) +
      Complex.I * conj (∫ θ in 0..(2 * π), F2 (γ θ) * deriv γ θ) := by
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
      simp 
      ring
    · have : IntervalIntegrable (fun θ => conj (F2 (γ θ) * deriv γ θ)) volume 0 (2 * π) := by
        rw [intervalIntegrable_iff] at hi2 ⊢
        exact (hi2.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
          hi2.aestronglyMeasurable) (Eventually.of_forall fun θ => by simp))
      simp_all
  rw [hdl, g1, integral_boundary_eq_dbar hb hL hγ hK2 hF2c]
  -- the interior side
  have hdi : ∀ {F : ℂ → ℂ} {K : NNReal}, LipschitzWith K F → IntegrableOn (dbar F) Ω := by
    intro F K hF
    exact Measure.integrableOn_of_bounded hb.measure_lt_top.ne (measurable_dbar F).aestronglyMeasurable
      (Eventually.of_forall (norm_dbar_le hF))
  have e : -Complex.I * (2 * Complex.I * ∫ z in Ω, dbar F1 z) +
      Complex.I * conj (2 * Complex.I * ∫ z in Ω, dbar F2 z) =
      ∫ z in Ω, (2 * dbar F1 z + 2 * conj (dbar F2 z)) := by
    rw [integral_add ((hdi hK1).const_mul _) (((hdi hK2).norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
      (hdi hK2).aestronglyMeasurable) (Eventually.of_forall fun z => by simp)).const_mul _), integral_const_mul,
      integral_const_mul, map_mul, integral_conj.symm]
    simp only [map_mul, map_ofNat, Complex.conj_I]
    ring_nf
    norm_num
  rw [e]
  refine setIntegral_congr_ae hΩo.measurableSet ?_
  filter_upwards [hV.ae_differentiableAt] with z hz _
  have hd1  := (hφt.dirD 1).1.differentiable (by simp)
  have hdI  := (hφt.dirD Complex.I).1.differentiable (by simp)
  have hqd  := hqt.1.differentiable (by simp) z
  have hfp : fderiv ℝ p z = (1 / 2 : ℂ) • fderiv ℝ (dirD φ 1) z +
      (-Complex.I / 2) • fderiv ℝ (dirD φ Complex.I) z := by
    simp_all [fderiv_fun_add ((hd1 z).const_mul _) ((hdI z).const_mul _), fderiv_const_mul (hd1 z), fderiv_const_mul (hdI z)]
  have hfq : fderiv ℝ q z = (1 / 2 : ℂ) • fderiv ℝ (dirD φ 1) z +
      (Complex.I / 2) • fderiv ℝ (dirD φ Complex.I) z := by
    simp_all [fderiv_fun_add ((hd1 z).const_mul _) ((hdI z).const_mul _), fderiv_const_mul (hdI z)]
  have hf1 : fderiv ℝ F1 z = V z • fderiv ℝ p z + p z • fderiv ℝ V z := fderiv_fun_mul hz (hpt.1.differentiable (by simp) z)
  have hf2 : fderiv ℝ F2 z = Complex.conjCLE.toContinuousLinearMap.comp
      (V z • fderiv ℝ q z + q z • fderiv ℝ V z) := by
    rw [← fderiv_fun_mul hz hqd]
    exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z (hz.mul hqd).hasFDerivAt).fderiv
  simp only [dbar, lap, hf1, hf2, hfp, hfq, Fin.sum_univ_two]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    map_add, map_mul, map_div₀, Complex.conj_conj, Complex.conj_I,
    map_ofNat, hp, hq, dirD, show coordDir 0 = 1 from rfl, show coordDir 1 = Complex.I from rfl]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Green's identity for the double layer: for `V` Lipschitz with compact support and trace
`h = V ∘ γ`, and `φ` smooth,
`μ_h(φ) = ∫_Ω (V Δφ + ∇V · ∇φ)`. -/
theorem doubleLayer_eq_integral (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {V : ℂ → ℂ} {K : NNReal} (hV : LipschitzWith K V)
    (hVc : HasCompactSupport V) {h : ℝ → ℂ} (hVh : ∀ θ ∈ Icc 0 (2 * π), V (γ θ) = h θ)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    doubleLayer γ h φ =
      ∫ z in Ω, (V z * lap φ z + ∑ i : Fin 2, dirD V (coordDir i) z * dirD φ (coordDir i) z) := by
  obtain ⟨R₀, hR₀⟩ := hb.closure.subset_ball 0
  set R := max R₀ 1 with hR
  have hcl : closure Ω ⊆ ball 0 R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  set φ' : ℂ → ℂ := fun z => b z * φ z with hφ'
  have hφ'd : ContDiff ℝ (⊤ : ℕ∞) φ' :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).mul hφ
  have heq : ∀ z ∈ ball 0 R, φ' =ᶠ[nhds z] φ := by
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    simp [hφ', b.one_of_mem_closedBall (ball_subset_closedBall hw)]
  have hD : ∀ z ∈ ball 0 R, fderiv ℝ φ' z = fderiv ℝ φ z := fun z hz =>
    (heq z hz).fderiv_eq
  have hdirD : ∀ v, ∀ z ∈ ball 0 R, dirD φ' v =ᶠ[nhds z] dirD φ v := by
    intro v z hz
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    simp [dirD, hD w hw]
  have hDD : ∀ v w, ∀ z ∈ ball 0 R, dirD (dirD φ' v) w z = dirD (dirD φ v) w z :=
    fun v w z hz => by simp [dirD, (hdirD v z hz).fderiv_eq]
  have hl : doubleLayer γ h φ' = doubleLayer γ h φ := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by positivity)] at hθ
    have  := hcl (frontier_subset_closure
      (hγ.image ▸ mem_image_of_mem γ hθ))
    simp_all
  rw [← hl, doubleLayer_eq_integral_of_hasCompactSupport hb hL hγ hV hVc hVh hφ'd (b.hasCompactSupport.comp_left  Complex.ofReal_zero).mul_right]
  refine setIntegral_congr_fun hL.1.1.measurableSet fun z hz => ?_
  have hz'  := hcl (subset_closure hz)
  have hlap : lap φ' z = lap φ z := by
    unfold lap; simp_all
  simp [hlap, dirD, hD z hz']

end PolyaNeumann
