module

public import RequestProject.ReconBasic
public import RequestProject.ArcLength

/-!
# The Cauchy–Pompeiu formula for Lipschitz functions

For a Lipschitz compactly supported `F : ℂ → ℂ` and every `w`,

  `∫_ℂ ∂̄F(z) / (z - w) dz = -π F(w)`  (`integral_dbar_div_sub`).

The proof is in polar coordinates around `w`: there
`r e^{-it} ∂̄F = (∂_r G + (i/r) ∂_t G)/2` for `G(r, t) = F(w + r e^{it})`; the radial term
integrates to `-F(w)` and the angular term to `0`. Rademacher's theorem and Fubini's theorem
make the computation valid for Lipschitz `F`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {F : ℂ → ℂ}

local notation "Φ0" => circleMap 0

lemma circleMap_zero_eq' r t :
    Φ0 r t = (r : ℂ) * Complex.exp (t * Complex.I) := by
  simp [circleMap]

lemma polarCoord_symm_eq_circleMap p :
    Complex.polarCoord.symm p = Φ0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- An `ℝ`-linear map evaluated at `e^{it}`. -/
lemma clm_apply_exp (L : ℂ →L[ℝ] ℂ) (t : ℝ) :
    L (Complex.exp (t * Complex.I)) = Real.cos t * L 1 + Real.sin t * L Complex.I := by
  rw [show Complex.exp (t * Complex.I) = Real.cos t • 1 + Real.sin t • Complex.I by
    rw [Complex.exp_mul_I, Complex.real_smul, Complex.real_smul, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, mul_one], map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

lemma clm_apply_I_mul_exp (L : ℂ →L[ℝ] ℂ) (t : ℝ) :
    L (Complex.I * Complex.exp (t * Complex.I)) =
      -Real.sin t * L 1 + Real.cos t * L Complex.I := by
  rw [show Complex.I * Complex.exp (t * Complex.I) = (-Real.sin t) • 1 + Real.cos t • Complex.I by
    rw [Complex.exp_mul_I, Complex.real_smul, Complex.real_smul, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- Points of differentiability of a Lipschitz function, in polar coordinates. -/
theorem integral_dbar_div_eq   (hF : LipschitzWith K F)
    (hFc : HasCompactSupport F) : ∫ z, dbar F z / z = -(π * F 0) := by
  obtain ⟨R₀, hR₀⟩ := hFc.isCompact.isBounded.subset_ball 0
  set R := max R₀ 1 with hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : ∀ z : ℂ, R ≤ ‖z‖ → z ∉ tsupport F := fun z hz hzs => by
    have := hR₀ hzs
    rw [mem_ball, dist_zero_right] at this
    linarith [le_max_left R₀ 1]
  have hD0 : ∀ z : ℂ, R ≤ ‖z‖ → fderiv ℝ F z = 0 := fun z hz =>
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (hsupp z hz)
  have hF0 : ∀ z : ℂ, R ≤ ‖z‖ → F z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (hsupp z hz)
  have hnorm : ∀ r t : ℝ, 0 ≤ r → ‖Φ0 r t‖ = r := fun r t hr => by
    simp [abs_of_nonneg hr]
  set A : ℝ × ℝ → ℂ := fun p => fderiv ℝ F (Φ0 p.1 p.2) (Complex.exp (p.2 * Complex.I))
    with hA
  set B : ℝ × ℝ → ℂ := fun p =>
    fderiv ℝ F (Φ0 p.1 p.2) (Complex.I * Complex.exp (p.2 * Complex.I)) with hB
  have hcm : Continuous fun p : ℝ × ℝ => Φ0 p.1 p.2 := by
    simp [circleMap_zero_eq']
    exact (Complex.continuous_ofReal.comp continuous_fst).mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hD1 :=
    (measurable_fderiv_apply_const ℝ F 1).comp hcm.measurable
  have hDI :=
    (measurable_fderiv_apply_const ℝ F Complex.I).comp hcm.measurable
  have hAb : ∀ p, ‖A p‖ ≤ K := fun p => by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [Complex.norm_exp_ofReal_mul_I, mul_one]
    exact norm_fderiv_le_of_lipschitz ℝ hF
  have hBb : ∀ p, ‖B p‖ ≤ K := fun p => by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, mul_one, mul_one]
    exact norm_fderiv_le_of_lipschitz ℝ hF
  -- the box
  set Q : Set (ℝ × ℝ) := Ioc 0 R ×ˢ Ioo (-π) π with hQ
  have hQt : Q ⊆ polarCoord.target := by
    rw [polarCoord_target]; exact prod_mono Ioc_subset_Ioi_self subset_rfl
  have hQfin : volume Q < ⊤ := by
    rw [hQ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioo_lt_top
  have hAi := Measure.integrableOn_of_bounded hQfin.ne
    (show Measurable A by
      have : A = fun p => Real.cos p.2 * fderiv ℝ F (Φ0 p.1 p.2) 1 +
          Real.sin p.2 * fderiv ℝ F (Φ0 p.1 p.2) Complex.I :=
        funext fun p => clm_apply_exp _ _
      rw [this]
      exact ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_snd)).measurable.mul
        hD1).add ((Complex.continuous_ofReal.comp
          (Real.continuous_sin.comp continuous_snd)).measurable.mul hDI)).aestronglyMeasurable (Eventually.of_forall hAb)
  have hBi := Measure.integrableOn_of_bounded hQfin.ne
    (show Measurable B by
      have : B = fun p => -Real.sin p.2 * fderiv ℝ F (Φ0 p.1 p.2) 1 +
          Real.cos p.2 * fderiv ℝ F (Φ0 p.1 p.2) Complex.I :=
        funext fun p => clm_apply_I_mul_exp _ _
      rw [this]
      exact ((Complex.continuous_ofReal.comp
        (Real.continuous_sin.comp continuous_snd)).measurable.neg.mul hD1).add
        ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_snd)).measurable.mul
          hDI)).aestronglyMeasurable (Eventually.of_forall hBb)
  -- polar coordinates
  rw [← Complex.integral_comp_polarCoord_symm]
  have hpt : ∀ p ∈ polarCoord.target, p.1 • (dbar F (Complex.polarCoord.symm p) /
      Complex.polarCoord.symm p) = (A p + Complex.I * B p) / 2 := by
    intro p hp
    rw [polarCoord_target] at hp
    have hr := Complex.ofReal_ne_zero.mpr hp.1.ne'
    rw [show (A p + Complex.I * B p) / 2 = Complex.exp (-(p.2 * Complex.I)) * dbar F (Φ0 p.1 p.2) by
      simp [hA, hB]; exact (show Complex.exp (-(p.2 * Complex.I)) * dbar F _ = (fderiv ℝ F _ (Complex.exp (p.2 * Complex.I)) + Complex.I * fderiv ℝ F _ (Complex.I * Complex.exp (p.2 * Complex.I))) / 2 by
        rw [clm_apply_exp, clm_apply_I_mul_exp, dbar, show Complex.exp (-(p.2 * Complex.I)) = Real.cos p.2 - Real.sin p.2 * Complex.I by
          rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I, Complex.ofReal_neg,
            Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
          ring]
        ring_nf
        rw [Complex.I_sq]
        ring).symm, polarCoord_symm_eq_circleMap, circleMap_zero_eq', Complex.real_smul]
    have hee : Complex.exp (-(p.2 * Complex.I)) * Complex.exp (p.2 * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    field_simp
    linear_combination (-(dbar F (p.1 * Complex.exp (p.2 * Complex.I)))) * hee
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hpt]
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero polarCoord.open_target.measurableSet hQt
    (by
      intro p hp
      obtain ⟨hpt, hpQ⟩ := hp
      rw [polarCoord_target] at hpt
      simp [hA, hB, (hD0 (Φ0 p.1 p.2) (by rw [hnorm p.1 p.2 hpt.1.le]; exact (show R < p.1 by
        by_contra hle
        exact hpQ ⟨⟨hpt.1, not_lt.mp hle⟩, hpt.2⟩).le))])]
  rw [integral_div, integral_add hAi (hBi.const_mul _), integral_const_mul]
  -- a.e. differentiability on the box, in product form
  have hae : ∀ᵐ p ∂((volume.restrict (Ioc 0 R)).prod (volume.restrict (Ioo (-π) π))),
      DifferentiableAt ℝ F (Φ0 p.1 p.2) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have h_inl : ∀ᵐ p ∂(volume.restrict polarCoord.target), DifferentiableAt ℝ F (Φ0 p.1 p.2) := by
      set S := {z | DifferentiableAt ℝ F z}ᶜ with hS
      have hSm : MeasurableSet S := (measurableSet_of_differentiableAt ℝ F).compl
      have hS0 : volume S = 0 := ae_iff.mp (hF.ae_differentiableAt (μ := volume))
      have hl := Complex.lintegral_comp_polarCoord_symm (S.indicator 1)
      rw [lintegral_indicator_one hSm, hS0, lintegral_eq_zero_iff' (by
        refine (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable.smul ?_
        exact ((measurable_one.indicator hSm).comp
          measurable_complexPolarCoord_symm).aemeasurable)] at hl
      filter_upwards [hl, ae_restrict_mem polarCoord.open_target.measurableSet] with p hp hpt
      simp only [Pi.zero_apply, smul_eq_mul, mul_eq_zero, ENNReal.ofReal_eq_zero, not_le.mpr (by
        rw [polarCoord_target] at hpt; exact hpt.1),
        false_or, indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false] at hp
      rw [hS, polarCoord_symm_eq_circleMap] at hp
      simpa using hp
    exact ae_restrict_of_ae_restrict_of_subset hQt h_inl
  have hPm : MeasurableSet {p : ℝ × ℝ | DifferentiableAt ℝ F (Φ0 p.1 p.2)} :=
    (measurableSet_of_differentiableAt ℝ F).preimage hcm.measurable
  have hae1 := Measure.ae_ae_of_ae_prod hae
  have hae2 := (Measure.ae_ae_comm hPm).mp hae1
  have hvolQ : volume.restrict Q = (volume.restrict (Ioc 0 R)).prod
      (volume.restrict (Ioo (-π) π)) := by
    rw [hQ, Measure.volume_eq_prod, Measure.prod_restrict]
  -- radial integrals
  -- angular integrals
  rw [show ∫ p in Q, A p = ∫ t in Ioo (-π) π, ∫ r in Ioc 0 R, A (r, t) by
    rw [hvolQ, integral_prod_symm A (by rw [← hvolQ]; exact hAi)], show ∫ p in Q, B p = ∫ r in Ioc 0 R, ∫ t in Ioo (-π) π, B (r, t) by
    rw [hvolQ, integral_prod B (by rw [← hvolQ]; exact hBi)], integral_congr_ae (show ∀ᵐ t ∂(volume.restrict (Ioo (-π) π)), ∫ r in Ioc 0 R, A (r, t) = -F 0 by
    filter_upwards [hae2] with t ht
    set g : ℝ → ℂ := fun r => F (Φ0 r t) with hg
    have hderiv : ∀ r, DifferentiableAt ℝ F (Φ0 r t) → deriv g r = A (r, t) := by
      intro r hr
      exact (hr.hasFDerivAt.comp_hasDerivAt r (by
        simp [circleMap_zero_eq']
        simpa using (hasDerivAt_id r).ofReal_comp.mul_const (Complex.exp (t * Complex.I)))).deriv
    rw [← intervalIntegral.integral_of_le hR0.le]
    have hcongr : ∫ r in 0..R, A (r, t) = ∫ r in 0..R, deriv g r := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hR0.le]
      filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp ht] with r hr hrI
      exact (hderiv r (hr hrI)).symm
    rw [hcongr, integral_deriv_of_lipschitz (by
      refine hF.comp (LipschitzWith.of_dist_le_mul (K := 1) fun r r' => ?_)
      rw [dist_eq_norm, circleMap_zero_eq', circleMap_zero_eq', ← sub_mul, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.dist_eq]
      simp)]
    simp only [hg, circleMap_zero_radius, Function.const_apply]
    rw [hF0 _ (by rw [hnorm _ _ hR0.le])]
    ring), integral_congr_ae (show ∀ᵐ r ∂(volume.restrict (Ioc 0 R)), ∫ t in Ioo (-π) π, B (r, t) = 0 by
    filter_upwards [hae1, ae_restrict_mem measurableSet_Ioc] with r hr hrI
    set k : ℝ → ℂ := fun t => F (Φ0 r t) with hk
    have hklip : LipschitzWith (K * Real.nnabs r) k := hF.comp (lipschitzWith_circleMap 0 r)
    have hr0 := Complex.ofReal_ne_zero.mpr hrI.1.ne'
    have hpi : -π ≤ π := by linarith [Real.pi_pos]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi]
    have hcongr : ∫ t in (-π)..π, B (r, t) = ∫ t in (-π)..π, (r : ℂ)⁻¹ * deriv k t := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hpi]
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hr, show ∀ᵐ t ∂volume, t ≠ π by
        simp [ae_iff]] with t ht htπ htI
      rw [(show ∀ t, DifferentiableAt ℝ F (Φ0 r t) → deriv k t = r * B (r, t) by
        intro t ht
        show deriv (F ∘ Φ0 r) t = _
        rw [(ht.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_circleMap 0 r t)).deriv, hB]
        simp only
        rw [circleMap_zero_eq', show r * Complex.exp (t * Complex.I) * Complex.I =
          r • (Complex.I * Complex.exp (t * Complex.I)) by rw [Complex.real_smul]; ring,
          map_smul, Complex.real_smul]) t (ht ⟨htI.1, lt_of_le_of_ne htI.2 htπ⟩)]
      field_simp
    rw [hcongr, intervalIntegral.integral_const_mul, integral_deriv_of_lipschitz hklip]
    simp only [hk]
    rw [show Φ0 r π = Φ0 r (-π) by
      rw [show π = -π + 2 * π by ring, periodic_circleMap]
      ring_nf, sub_self, mul_zero])]
  simp only [integral_const, smul_zero, mul_zero, add_zero]
  rw [measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]),
    Complex.real_smul]
  push_cast
  ring

/-- **Cauchy–Pompeiu formula.** For a Lipschitz compactly supported `F`,
`∫_ℂ ∂̄F(z)/(z - w) dz = -π F(w)`. -/
theorem integral_dbar_div_sub   (hF : LipschitzWith K F)
    (hFc : HasCompactSupport F) w : ∫ z, dbar F z / (z - w) = -(π * F w) := by
  set G : ℂ → ℂ := fun z => F (z + w) with hG
  have hdb : ∀ z, dbar G z = dbar F (z + w) := fun z => by
    simp [dbar, hG]
    rw [fderiv_comp_add_right]
  have h := integral_dbar_div_eq (show LipschitzWith K G by
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    simpa [hG] using (hF.dist_le_mul (z + w) (z' + w))) (hFc.comp_homeomorph (Homeomorph.addRight w))
  rw [show ∫ z, dbar G z / z = ∫ z, dbar F (z + w) / z by simp_rw [hdb]] at h
  simp [hG] at h
  rw [← h, ← integral_add_right_eq_self (fun z => dbar F z / (z - w)) w]
  simp

end PolyaNeumann
