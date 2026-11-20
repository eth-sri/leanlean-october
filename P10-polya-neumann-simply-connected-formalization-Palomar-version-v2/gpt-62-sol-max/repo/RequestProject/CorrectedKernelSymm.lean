module

public import RequestProject.CorrectedKernelSmooth
public import RequestProject.MatrixHS

/-!
# Hermitian symmetry of the corrected kernel (Lemma 6.6, second variable)

The operator `i(T_E - T_E^*) + O_E B_E O_E^*` is self-adjoint, and so is `2D^{-1}`; accordingly
the corrected kernel is Hermitian:

  `r_E(θ, t) = conj (r_E(t, θ))`  (`correctedKernel_conj_symm`),

because `w_E(θ, t) = conj (w_E(t, θ))` and `B_E` is self-adjoint (Lemma 6.3). For a bounded,
jointly measurable Hermitian kernel on `[0, L]²` the double Fourier coefficients satisfy
`k_{n m} = conj (k_{-m, -n})` (`doubleCoeff_conj_symm`, by Fubini). Hence the fractional
gain of `summable_rpow_mul_correctedKernelCoeff` in the first variable transfers to the second
variable (`summable_rpow_mul_correctedKernelCoeff_snd`), as in the paper:

  `∑_{n, m} |n|^{2+2δ} |r_{n m}|² < ∞`  for `0 ≤ δ < 1/2`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

/-- **Fubini for a Hermitian kernel.** For a bounded, jointly measurable kernel on `[0, 2π]²`
with `k(θ, t) = conj (k(t, θ))`, the double Fourier integrals satisfy
`∫∫ e_{-m}(θ) e_{-n}(t) k(θ, t) = conj (∫∫ e_n(θ) e_m(t) k(θ, t))`. -/
lemma doubleIntegral_conj_symm {k : ℝ → ℝ → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry k)
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))))
    (hb : ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π), ‖k θ t‖ ≤ C)
    (hs : ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π), k θ t = conj (k t θ)) (n m : ℤ) :
    ∫ θ in Ioc 0 (2 * π), fourier (-m) (θ : AddCircle (2 * π - 0)) *
        ∫ t in Ioc 0 (2 * π), fourier (-n) (t : AddCircle (2 * π - 0)) * k θ t =
      conj (∫ θ in Ioc 0 (2 * π), fourier n (θ : AddCircle (2 * π - 0)) *
        ∫ t in Ioc 0 (2 * π), fourier m (t : AddCircle (2 * π - 0)) * k θ t) := by
  simp only [← integral_const_mul]
  set μ := volume.restrict (Ioc (0:ℝ) (2 * π))
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩; simp
  set e : ℤ → ℝ → ℂ := fun j x => fourier j (x : AddCircle (2 * π - 0)) with he
  have hec : ∀ j, Continuous (e j) := fun j => (map_continuous (fourier j)).comp
    (AddCircle.continuous_mk' _)
  have hen : ∀ j x, ‖e j x‖ = 1 := fun j x => by
    simp only [he]; rw [fourier_apply]; exact Circle.norm_coe _
  have hconj : ∀ j x, conj (e j x) = e (-j) x := fun j x => by simp only [he, fourier_neg]
  have hae : ∀ᵐ p ∂(μ.prod μ), p ∈ Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π) := by
    simp only [μ]; rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hmS :=
    hm.comp_measurePreserving (Measure.measurePreserving_swap)
  have hint : Integrable (Function.uncurry fun θ t =>
      e (-m) θ * (e (-n) t * conj (k t θ))) (μ.prod μ) := by
    refine Integrable.of_bound (C := C) ?_ ?_
    · exact ((hec _).comp continuous_fst).aestronglyMeasurable.mul
        (((hec _).comp continuous_snd).aestronglyMeasurable.mul
          (Complex.continuous_conj.comp_aestronglyMeasurable hmS))
    · filter_upwards [hae] with p hp
      simp  [Function.uncurry, hen]
      grind
  have h1 : ∫ θ, ∫ t, e (-m) θ * (e (-n) t * k θ t) ∂μ ∂μ =
      ∫ θ, ∫ t, e (-m) θ * (e (-n) t * conj (k t θ)) ∂μ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    grind
  change ∫ θ, ∫ t, e (-m) θ * (e (-n) t * k θ t) ∂μ ∂μ =
    conj (∫ θ, ∫ t, e n θ * (e m t * k θ t) ∂μ ∂μ)
  rw [h1, integral_integral_swap hint, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  dsimp 
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp  [hconj]
  ring

/-- **Double Fourier coefficients of a Hermitian kernel.** For a bounded, jointly measurable
kernel on `[0, 2π]²` with `k(θ, t) = conj (k(t, θ))`, the coefficient `k_{n m}` (frequency `n`
in `t`, `m` in `θ`) is `conj (k_{-m, -n})`. -/
theorem doubleCoeff_conj_symm {k : ℝ → ℝ → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry k)
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))))
    (hb : ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π), ‖k θ t‖ ≤ C)
    (hs : ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π), k θ t = conj (k t θ)) (n m : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) n) m =
      conj (fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) (-m)) (-n)) := by
  simp only [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le two_pi_pos.le,
    smul_eq_mul, neg_neg, Complex.real_smul]
  set c : ℂ := ((1 / (2 * π - 0) : ℝ) : ℂ)
  simp only [mul_left_comm _ c, integral_const_mul]
  rw [doubleIntegral_conj_symm hm hb hs n m]
  simp only [map_mul, c, Complex.conj_ofReal]

variable {γ : ℝ → ℂ} {K K' : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

section

variable (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
include hK hW

/-- `B_E` is self-adjoint (Lemma 6.3), with no assumption on `c_E`. -/
lemma cutBE_isSelfAdjoint  :
    IsSelfAdjoint (cutBE W) :=
  cutB_isSelfAdjoint (inner_cutD_cutC (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩) _)

/-- **Hermitian symmetry of the corrected kernel:** `r_E(θ, t) = conj (r_E(t, θ))`. -/
theorem correctedKernel_conj_symm 
    (θ t : ℝ) : correctedKernel W θ t = conj (correctedKernel W t θ) := by
  have hB := cutBE_isSelfAdjoint hK hW
  have hw : volterraKernel W θ t = conj (volterraKernel W t θ) := by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.adjoint_inner_left]
    simp
  have hb : ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W t) (basisVec 0)))⟫_ℂ =
      conj ⟪basisVec 0, W t (cutBE W (ContinuousLinearMap.adjoint (W θ) (basisVec 0)))⟫_ℂ := by
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.adjoint_inner_left (cutBE W), hB.adjoint_eq,
      ContinuousLinearMap.adjoint_inner_right]
  have hsign : Real.sign (θ - t) = -Real.sign (t - θ) := by
    rw [← Real.sign_neg, neg_sub]
  simp only [correctedKernel, map_add, map_mul, map_sub, Complex.conj_I, Complex.conj_ofReal,
    map_div₀, map_one, hw, hb, hsign, Complex.ofReal_neg]
  ring

end

/-- Joint measurability of the corrected kernel on `[0, L]²`. -/
lemma aestronglyMeasurable_correctedKernel (hW : IsTransport γ E W) :
    AEStronglyMeasurable (Function.uncurry (correctedKernel W))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))) := by
  have hWc :=
    hW.1.comp_continuous continuous_clampTwoPi clampTwoPi_mem
  have hx : Continuous fun t => ContinuousLinearMap.adjoint (W (clampTwoPi t)) (basisVec 0) :=
    ((ContinuousLinearMap.adjoint.toLinearIsometry.continuous.comp hWc).clm_apply
      continuous_const)
  have hmeas : Measurable fun p : ℝ × ℝ =>
      correctedKernel W (clampTwoPi p.1) (clampTwoPi p.2) := by
    have h1 :=
      Complex.measurable_ofReal.comp (measurable_real_sign.comp
        ((continuous_clampTwoPi.comp continuous_fst).sub
          (continuous_clampTwoPi.comp continuous_snd)).measurable)
    have h2 : Continuous fun p : ℝ × ℝ =>
        volterraKernel W (clampTwoPi p.1) (clampTwoPi p.2) := by
      unfold volterraKernel
      exact continuous_const.inner ((hWc.comp continuous_fst).clm_apply (hx.comp continuous_snd))
    have h3 : Continuous fun p : ℝ × ℝ => ⟪basisVec 0, W (clampTwoPi p.1) (cutBE W
        (ContinuousLinearMap.adjoint (W (clampTwoPi p.2)) (basisVec 0)))⟫_ℂ :=
      continuous_const.inner ((hWc.comp continuous_fst).clm_apply
        ((cutBE W).continuous.comp (hx.comp continuous_snd)))
    have h4 : Continuous fun p : ℝ × ℝ =>
        Complex.I * (((clampTwoPi p.1 : ℂ) - (clampTwoPi p.2 : ℂ)) / (π : ℂ)) :=
      continuous_const.mul (((Complex.continuous_ofReal.comp
        (continuous_clampTwoPi.comp continuous_fst)).sub
        (Complex.continuous_ofReal.comp (continuous_clampTwoPi.comp continuous_snd))).div_const _)
    unfold correctedKernel
    exact ((measurable_const.mul h1).mul (h2.measurable.sub measurable_const)).add
      h4.measurable |>.add h3.measurable
  refine hmeas.aestronglyMeasurable.congr ?_
  have hae : ∀ᵐ p ∂((volume.restrict (Ioc (0:ℝ) (2 * π))).prod
      (volume.restrict (Ioc (0:ℝ) (2 * π)))), p ∈ Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π) := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  filter_upwards [hae] with p hp
  simp  [Function.uncurry]
  rw [clampTwoPi_of_mem (Ioc_subset_Icc_self hp.1), clampTwoPi_of_mem (Ioc_subset_Icc_self hp.2)]

section

variable (hK : LipschitzWith K γ)
include hK

/-- The double Fourier coefficients of the corrected kernel satisfy `r_{n m} = conj (r_{-m,-n})`. -/
theorem correctedKernelCoeff_conj_symm  (hW : IsTransport γ E W)
    (n m : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) n) m =
      conj (fourierCoeffOn two_pi_pos
        (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) (-m)) (-n)) :=
  doubleCoeff_conj_symm (aestronglyMeasurable_correctedKernel hW)
    (fun _ hθ _ ht => norm_correctedKernel_le hK hW hθ ht)
    (fun θ _ t _ => correctedKernel_conj_symm hK hW θ t) n m

end

end PolyaNeumann
