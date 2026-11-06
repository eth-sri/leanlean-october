module

public import RequestProject.MollifierL2
public import RequestProject.BiLipschitz
public import RequestProject.WeakCompact

/-!
# The Sobolev chain rule for bi-Lipschitz maps

For a homeomorphism `f` of the plane which is `K`-Lipschitz on an open set `Ω` with inverse
`K`-Lipschitz on `f(Ω)`, and `v ∈ H¹(f(Ω))` with weak gradient `G`, the function `u = v ∘ f` lies in
`H¹(Ω)` with weak gradient `∂_i u = ∑_j (∂_i f)_j (G_j ∘ f)`, i.e. `∇u = (Df)ᵀ (∇v ∘ f)`
(`isWeakGradient_comp_bilip`).

The proof mollifies `v`: `ψ_k = ρ_k ⋆ v` is smooth with `∇ψ_k = ρ_k ⋆ G` near `f(supp θ)`, the
chain rule for `ψ_k ∘ f` holds by integration by parts for Lipschitz functions (Rademacher), and
`ψ_k → v`, `∇ψ_k → G` in `L²` (`tendsto_mollify_L2`).
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace PolyaNeumann

/-! ### Derivatives of mollifications of `H¹` functions -/

variable {Ω : Set ℂ} {C : ℝ≥0}

/-- The weak gradient identity tested against the reflected bump `t ↦ ρ(x - t)`. -/
lemma integral_fderiv_bump_smul_eq (hΩ : IsOpen Ω) {v : L2 Ω} {G : Fin 2 → L2 Ω}
    (hG : IsWeakGradient Ω v G) (φ : ContDiffBump (0 : ℂ)) (x : ℂ)
    (hx : closedBall x φ.rOut ⊆ Ω) (i : Fin 2) :
    ∫ t, fderiv ℝ (φ.normed volume) (x - t) (coordDir i) • extZero Ω v t =
      ∫ t, φ.normed volume (x - t) • extZero Ω (G i) t := by
  have h := hG (reflBump φ x) (testFunction_reflBump φ x hx) i
  simp_rw [fderiv_reflBump] at h
  have e1 : ∀ t, fderiv ℝ (φ.normed volume) (x - t) (coordDir i) • extZero Ω v t =
      Ω.indicator (fun t => -(v t *
        -fderiv ℝ (φ.normed volume) (x - t) (coordDir i))) t := by
    intro t
    by_cases ht : t ∈ Ω
    all_goals simp [extZero, ht, mul_comm]
  have e2 : ∀ t, φ.normed volume (x - t) • extZero Ω (G i) t =
      Ω.indicator (fun t => G i t * reflBump φ x t) t := by
    intro t
    by_cases ht : t ∈ Ω
    all_goals simp [extZero, reflBump, ht, mul_comm]
  simp_all [integral_indicator hΩ.measurableSet, integral_neg]

/-- The mollification of an `H¹` function is differentiated by mollifying its weak gradient. -/
lemma fderiv_mollify_extZero (hΩ : IsOpen Ω) {v : L2 Ω} {G : Fin 2 → L2 Ω}
    (hG : IsWeakGradient Ω v G) (φ : ContDiffBump (0 : ℂ)) (x : ℂ)
    (hx : closedBall x φ.rOut ⊆ Ω) (i : Fin 2) :
    fderiv ℝ (mollify (φ.normed volume) (extZero Ω v)) x (coordDir i) =
      mollify (φ.normed volume) (extZero Ω (G i)) x := by
  have hV : LocallyIntegrable (extZero Ω v) volume :=
    locallyIntegrable_indicator_L2 hΩ.measurableSet v
  have hint := HasCompactSupport.convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
    ((φ.hasCompactSupport_normed (μ := volume)).fderiv ℝ)
    ((φ.contDiff_normed (n := 1)).continuous_fderiv (by simp)) hV x
  unfold mollify
  rw [(HasCompactSupport.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.hasCompactSupport_normed ) (φ.contDiff_normed ) hV x).fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  rw [← integral_sub_left_eq_self _ volume x]
  simp only [sub_sub_cancel]
  rw [integral_fderiv_bump_smul_eq hΩ hG φ x hx i, convolution_def,
    ← integral_sub_left_eq_self _ volume x]
  simp 

/-! ### Integration by parts for Lipschitz functions -/

/-- Integration by parts for a real Lipschitz function against a `C¹` compactly supported function
(from Rademacher's theorem). -/
lemma integral_fderiv_mul_real {F θ : ℂ → ℝ} (hF : LipschitzWith C F)
    (hθ : ContDiff ℝ 1 θ) (hθs : HasCompactSupport θ) (e : ℂ) :
    ∫ x, fderiv ℝ F x e * θ x = -∫ x, F x * fderiv ℝ θ x e := by
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hθs hθ (by norm_num)
  have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume) hF hD hθs e
  have h1 : ∫ x, lineDeriv ℝ F x e * θ x = ∫ x, fderiv ℝ F x e * θ x := by
    refine integral_congr_ae ?_
    filter_upwards [hF.ae_differentiableAt] with x hx
    rw [hx.lineDeriv_eq_fderiv]
  have h2 : ∫ x, lineDeriv ℝ θ x (-e) * F x = -∫ x, F x * fderiv ℝ θ x e := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [((hθ.differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
    ring
  linarith

/-- Integration by parts for a complex Lipschitz function against a `C¹` compactly supported
function: `∫ F ∂_e θ = -∫ (∂_e F) θ`, with `∂_e F` the a.e. defined derivative. -/
lemma integral_mul_fderiv_of_lipschitz {F θ : ℂ → ℂ} (hF : LipschitzWith C F)
    (hθ : ContDiff ℝ 1 θ) (hθs : HasCompactSupport θ) (e : ℂ) :
    ∫ x, F x * fderiv ℝ θ x e = -∫ x, fderiv ℝ F x e * θ x := by
  set Fr : ℂ → ℝ := fun x => (F x).re
  set Fi : ℂ → ℝ := fun x => (F x).im
  set θr : ℂ → ℝ := fun x => (θ x).re
  set θi : ℂ → ℝ := fun x => (θ x).im
  have hFr : LipschitzWith _ Fr := Complex.reCLM.lipschitz.comp hF
  have hFi : LipschitzWith _ Fi := Complex.imCLM.lipschitz.comp hF
  have hθr : ContDiff ℝ 1 θr := Complex.reCLM.contDiff.comp hθ
  have hθi : ContDiff ℝ 1 θi := Complex.imCLM.contDiff.comp hθ
  have hθrs : HasCompactSupport θr := hθs.comp_left  (by simp)
  have hθis : HasCompactSupport θi := hθs.comp_left  (by simp)
  have hdθ  := hθ.differentiable one_ne_zero
  have dθr : ∀ x, fderiv ℝ θr x e = (fderiv ℝ θ x e).re := fun x => DFunLike.congr_fun ((Complex.reCLM.hasFDerivAt).comp x (hdθ x).hasFDerivAt).fderiv e
  have dθi : ∀ x, fderiv ℝ θi x e = (fderiv ℝ θ x e).im := fun x => DFunLike.congr_fun ((Complex.imCLM.hasFDerivAt).comp x (hdθ x).hasFDerivAt).fderiv e
  have dF : ∀ᵐ x, fderiv ℝ Fr x e = (fderiv ℝ F x e).re ∧ fderiv ℝ Fi x e = (fderiv ℝ F x e).im := by
    filter_upwards [hF.ae_differentiableAt] with x hx
    exact ⟨DFunLike.congr_fun ((Complex.reCLM.hasFDerivAt).comp x hx.hasFDerivAt).fderiv e,
      DFunLike.congr_fun ((Complex.imCLM.hasFDerivAt).comp x hx.hasFDerivAt).fderiv e⟩
  -- integrability
  have hcs : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → Integrable g :=
    fun g hg hgs => hg.integrable_of_hasCompactSupport hgs
  have hdcont : ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g → Continuous fun x => fderiv ℝ g x e :=
    fun hg => (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdsupp : ∀ {g : ℂ → ℝ}, HasCompactSupport g → HasCompactSupport fun x => fderiv ℝ g x e :=
    fun hg => (hg.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℝ => T e) rfl
  have hbd : ∀ {c : ℝ≥0} {G : ℂ → ℝ} (g : ℂ → ℝ), LipschitzWith c G → Continuous g →
      HasCompactSupport g → Integrable (fun x => fderiv ℝ G x e * g x) := by
    intro c G g hG hg hgs
    refine (hcs g hg hgs).bdd_mul (c := c * ‖e‖)
      (measurable_fderiv_apply_const ℝ G e).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hG) (norm_nonneg _))
  have i1  :=
    hcs _ (hFr.continuous.mul (hdcont hθr)) (hdsupp hθrs).mul_left
  have i2  :=
    hcs _ (hFi.continuous.mul (hdcont hθi)) (hdsupp hθis).mul_left
  have i3  :=
    hcs _ (hFr.continuous.mul (hdcont hθi)) (hdsupp hθis).mul_left
  have i4  :=
    hcs _ (hFi.continuous.mul (hdcont hθr)) (hdsupp hθrs).mul_left
  have j1 := hbd θr hFr hθr.continuous hθrs
  have j2 := hbd θi hFi hθi.continuous hθis
  have I1 : Integrable fun x => F x * fderiv ℝ θ x e := by
    refine (hF.continuous.mul ((hθ.continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport ?_
    exact ((hθs.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℂ => T e) (by simp)).mul_left
  have I2 : Integrable fun x => fderiv ℝ F x e * θ x := by
    refine (hθ.continuous.integrable_of_hasCompactSupport hθs).bdd_mul (c := C * ‖e‖)
      (measurable_fderiv_apply_const ℝ F e).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg _))
  apply Complex.ext
  · rw [Complex.neg_re, show (∫ x, F x * fderiv ℝ θ x e).re = ∫ x, (F x * fderiv ℝ θ x e).re from
      (integral_re I1).symm, show (∫ x, fderiv ℝ F x e * θ x).re =
      ∫ x, (fderiv ℝ F x e * θ x).re from (integral_re I2).symm]
    have e1 : ∫ x, (F x * fderiv ℝ θ x e).re =
        (∫ x, Fr x * fderiv ℝ θr x e) - ∫ x, Fi x * fderiv ℝ θi x e := by
      refine Eq.trans ?_ (integral_sub i1 i2)
      simp [Fr, Fi, dθr, dθi]
    have e2 : ∫ x, (fderiv ℝ F x e * θ x).re =
        (∫ x, fderiv ℝ Fr x e * θr x) - ∫ x, fderiv ℝ Fi x e * θi x := by
      refine Eq.trans ?_ (integral_sub j1 j2)
      refine integral_congr_ae ?_
      filter_upwards [dF] with x hx
      simp [θr, θi, hx.1, hx.2]
    rw [e1, e2, integral_fderiv_mul_real hFr hθr hθrs e, integral_fderiv_mul_real hFi hθi hθis e]; ring
  · rw [Complex.neg_im, show (∫ x, F x * fderiv ℝ θ x e).im = ∫ x, (F x * fderiv ℝ θ x e).im from
      (integral_im I1).symm, show (∫ x, fderiv ℝ F x e * θ x).im =
      ∫ x, (fderiv ℝ F x e * θ x).im from (integral_im I2).symm]
    have e1 : ∫ x, (F x * fderiv ℝ θ x e).im =
        (∫ x, Fr x * fderiv ℝ θi x e) + ∫ x, Fi x * fderiv ℝ θr x e := by
      refine Eq.trans ?_ (integral_add i3 i4)
      simp [Fr, Fi, dθr, dθi]
    have e2 : ∫ x, (fderiv ℝ F x e * θ x).im =
        (∫ x, fderiv ℝ Fr x e * θi x) + ∫ x, fderiv ℝ Fi x e * θr x := by
      refine Eq.trans ?_ (integral_add (hbd θi hFr hθi.continuous hθis) (hbd θr hFi hθr.continuous hθrs))
      refine integral_congr_ae ?_
      filter_upwards [dF] with x hx
      simp [θr, θi, hx.1, hx.2]
    rw [e1, e2, integral_fderiv_mul_real hFr hθi hθis e, integral_fderiv_mul_real hFi hθr hθrs e]; ring

/-- The chain rule `∂_e (ψ ∘ f) = Dψ(f) (∂_e f)` for a `C¹` function `ψ` and a map `f` which is
Lipschitz on an open set `U`, in weak form against test functions on `U`. -/
lemma setIntegral_comp_mul_fderiv {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f U) {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) {θ : ℂ → ℂ}
    (hθ : TestFunction U θ) (e : ℂ) :
    ∫ x in U, ψ (f x) * fderiv ℝ θ x e =
      -∫ x in U, fderiv ℝ ψ (f x) (fderiv ℝ f x e) * θ x := by
  obtain ⟨hθc, hθs, hθU⟩ := hθ
  obtain ⟨R, hR⟩ := hθs.isCompact.isBounded.subset_ball 0
  obtain ⟨f', hf', hff'⟩ := hf.extend_finite_dimension
  obtain ⟨R', hR'⟩ := (hf'.isBounded_image (isBounded_ball  )).subset_closedBall 0
  obtain ⟨Kψ, hKψ⟩ := (hψ.contDiffOn ).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall 0 R') (isCompact_closedBall 0 R')
  obtain ⟨F, hF, hFeq⟩ := (hKψ.comp (hf'.lipschitzOnWith) (fun x hx => hR' (mem_image_of_mem f' hx))).extend_finite_dimension
  set W := U ∩ ball 0 R
  have hKW  := subset_inter hθU hR
  have hFW : ∀ x ∈ W, F x = ψ (f x) := fun x hx => by
    rw [← hFeq hx.2]; simp [hff' hx.1]
  have hdθ0 : ∀ x ∉ tsupport θ, fderiv ℝ θ x e = 0 := fun x hx => by
    rw [Function.notMem_support.mp
      (fun h => hx (support_fderiv_subset ℝ h))]
    rfl
  have hθ0 : ∀ x ∉ tsupport θ, θ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have L : ∫ x in U, ψ (f x) * fderiv ℝ θ x e = ∫ x, F x * fderiv ℝ θ x e := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ tsupport θ
      · simp [hFW x (hKW hx)]
      simp_all
    · intro x hx
      simp [hdθ0 x (fun h => hx (hθU h))]
  have Rr : ∫ x in U, fderiv ℝ ψ (f x) (fderiv ℝ f x e) * θ x = ∫ x, fderiv ℝ F x e * θ x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero  (f := fun x => fderiv ℝ F x e * θ x)
      (fun x hx => by simp [hθ0 x (fun h => hx (hθU h))])]
    refine setIntegral_congr_ae hU.measurableSet ?_
    have hd := ae_differentiableAt_of_lipschitzOnWith hU hf
    rw [ae_restrict_iff' hU.measurableSet] at hd
    filter_upwards [hd] with x hdx hxU
    by_cases hx : x ∈ tsupport θ
    · have hev : F =ᶠ[𝓝 x] ψ ∘ f :=
        Filter.eventually_of_mem ((hU.inter isOpen_ball).mem_nhds (hKW hx)) fun y hy => hFW y hy
      rw [hev.fderiv_eq, fderiv_comp x ((hψ.differentiable one_ne_zero) _) (hdx hxU)]
      rfl
    simp_all
  rw [L, Rr, integral_mul_fderiv_of_lipschitz hF (hθc.of_le (by norm_num)) hθs e]

/-! ### Composition with a bi-Lipschitz map in `L²` -/

section BiLip

variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : ℝ≥0}

lemma lintegral_comp_bilip_le (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) (h : ℂ → ℝ≥0∞) :
    ∫⁻ x in Ω, h (f x) ≤ K ^ 2 * ∫⁻ y in f '' Ω, h y := by
  calc ∫⁻ x in Ω, h (f x)
      ≤ ∫⁻ x in Ω, K ^ 2 * (ENNReal.ofReal |(fderiv ℝ f x).det| * h (f x)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_inv_sq_le_abs_det hΩ hf hg] with x hx
        have h2 : 1 ≤ K ^ 2 * ENNReal.ofReal |(fderiv ℝ f x).det| := by
          simpa using ENNReal.ofReal_le_ofReal ((inv_le_iff_one_le_mul₀' (by positivity)).mp hx)
        calc h (f x) = 1 * h (f x) := (one_mul _).symm
          _ ≤ _ := by rw [← mul_assoc]; gcongr
    _ = K ^ 2 * ∫⁻ y in f '' Ω, h y := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_image_bilip hΩ hf]

lemma eLpNorm_comp_bilip_le (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) (H : ℂ → ℂ) :
    eLpNorm (fun x => H (f x)) 2 (volume.restrict Ω) ≤
      K * eLpNorm H 2 (volume.restrict (f '' Ω)) := by
  by_cases hH : AEStronglyMeasurable H (volume.restrict (f '' Ω))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hH,
      ENNReal.mul_top (by exact_mod_cast hK.ne')]
    exact le_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (show AEStronglyMeasurable (fun x => H (f x)) (volume.restrict Ω) from
        hH.comp_quasiMeasurePreserving (quasiMeasurePreserving_restrict hg)),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hH]
  calc (∫⁻ x in Ω, ‖H (f x)‖ₑ ^ (2:ℝ)) ^ (1 / 2 : ℝ)
      ≤ (K ^ 2 * ∫⁻ y in f '' Ω, ‖H y‖ₑ ^ (2:ℝ)) ^ (1 / 2 : ℝ) := by
        gcongr; exact lintegral_comp_bilip_le hΩ hK hf hg (fun y => ‖H y‖ₑ ^ 2)
    _ = K * (∫⁻ y in f '' Ω, ‖H y‖ₑ ^ (2:ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

lemma memLp_comp_bilip' (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) {H : ℂ → ℂ}
    (hH : MemLp H 2 (volume.restrict (f '' Ω))) :
    MemLp (fun x => H (f x)) 2 (volume.restrict Ω) :=
  (lt_of_le_of_lt (eLpNorm_comp_bilip_le hΩ hK hf hg H)
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hH.eLpNorm_lt_top))

/-- Cauchy–Schwarz for `∫ A B` with respect to an arbitrary measure. -/
lemma norm_integral_mul_le_eLpNorm {μ : Measure ℂ} {A B : ℂ → ℂ} (hA : MemLp A 2 μ)
    (hB : MemLp B 2 μ) :
    ‖∫ x, A x * B x ∂μ‖ ≤ (eLpNorm A 2 μ).toReal * (eLpNorm B 2 μ).toReal := by
  have hA'  := hA.star
  have key : ∫ x, A x * B x ∂μ = inner ℂ (hA'.toLp _) (hB.toLp _) := by
    refine integral_congr_ae ?_
    filter_upwards [hA'.coeFn_toLp, hB.coeFn_toLp] with x h1 h2
    simp [h1, h2, mul_comm]
  rw [key]
  refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
  simp

/-- If `W_k → W` in `L²(ℂ)`, then `∫_Ω (W_k ∘ f) c → ∫_Ω (W ∘ f) c` for `c ∈ L²(Ω)`. -/
lemma tendsto_setIntegral_comp_mul (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) {W : ℕ → ℂ → ℂ} {W₀ : ℂ → ℂ}
    (hW : ∀ k, MemLp (W k) 2 volume) (hW₀ : MemLp W₀ 2 volume)
    (hconv : Tendsto (fun k => eLpNorm (W k - W₀) 2 volume) atTop (𝓝 0)) {c : ℂ → ℂ}
    (hc : MemLp c 2 (volume.restrict Ω)) :
    Tendsto (fun k => ∫ x in Ω, W k (f x) * c x) atTop (𝓝 (∫ x in Ω, W₀ (f x) * c x)) := by
  have hm : ∀ {H : ℂ → ℂ}, MemLp H 2 volume → MemLp (fun x => H (f x)) 2 (volume.restrict Ω) :=
    fun hH => memLp_comp_bilip' hΩ hK hf hg (hH.restrict _)
  have hint : ∀ {H : ℂ → ℂ}, MemLp H 2 volume →
      Integrable (fun x => H (f x) * c x) (volume.restrict Ω) :=
    fun hH => (hm hH).integrable_mul hc
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ k, ‖(∫ x in Ω, W k (f x) * c x) - ∫ x in Ω, W₀ (f x) * c x‖ ≤
      (K * eLpNorm (W k - W₀) 2 volume).toReal * (eLpNorm c 2 (volume.restrict Ω)).toReal := by
    intro k
    rw [← integral_sub (hint (hW k)) (hint hW₀)]
    have e : (fun x => W k (f x) * c x - W₀ (f x) * c x) = fun x => (W k - W₀) (f x) * c x := by
      simp [sub_mul]
    rw [e]
    refine (norm_integral_mul_le_eLpNorm (hm ((hW k).sub hW₀)) hc).trans ?_
    gcongr
    · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ((hW k).sub hW₀).eLpNorm_ne_top
    · exact (eLpNorm_comp_bilip_le hΩ hK hf hg _).trans
        (mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _)
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  have : Tendsto (fun k => (K * eLpNorm (W k - W₀) 2 volume).toReal) atTop (𝓝 0) := by
    refine (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ?_
    simpa using ENNReal.Tendsto.const_mul hconv (Or.inr ENNReal.coe_ne_top)
  simpa using this.mul_const _

end BiLip

/-! ### The chain rule -/

section ChainRule

variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : ℝ≥0}

/-- The real coordinates `(Re w, Im w)` of `w ∈ ℂ = ℝ²`. -/
def coordRe (j : Fin 2) (w : ℂ) : ℝ := ![w.re, w.im] j

lemma clm_apply_eq_sum_coordRe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : ℂ →L[ℝ] E) (w : ℂ) : T w = ∑ j, (coordRe j w : ℂ) • T (coordDir j) := by
  have hw : w = w.re • 1 + w.im • Complex.I := by norm_num
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul]
  simp [coordRe, coordDir]

lemma abs_coordRe_le (j : Fin 2) (w : ℂ) : |coordRe j w| ≤ ‖w‖ := by
  fin_cases j
  · exact Complex.abs_re_le_norm w
  · exact Complex.abs_im_le_norm w

lemma norm_coordDir (i : Fin 2) : ‖coordDir i‖ = 1 := by
  fin_cases i <;> simp [coordDir]

lemma measurable_coordRe_fderiv (f : ℂ → ℂ) (i j : Fin 2) :
    Measurable fun x => coordRe j (fderiv ℝ f x (coordDir i)) := by
  fin_cases j
  · exact Complex.measurable_re.comp (measurable_fderiv_apply_const ℝ f _)
  · exact Complex.measurable_im.comp (measurable_fderiv_apply_const ℝ f _)

lemma memLp_mollify (φ : ContDiffBump (0 : ℂ)) {H : ℂ → ℂ} (hH : MemLp H 2 volume) :
    MemLp (mollify (φ.normed volume) H) 2 volume :=
  ((eLpNorm_mollify_le φ hH.aestronglyMeasurable).trans_lt hH.eLpNorm_lt_top)

/-- The chain rule gradient `∂_i (v ∘ f) = ∑_j (∂_i f)_j (G_j ∘ f)`. -/
def chainGrad (f : ℂ → ℂ) (G : Fin 2 → ℂ → ℂ) (i : Fin 2) (x : ℂ) : ℂ :=
  ∑ j, (coordRe j (fderiv ℝ f x (coordDir i)) : ℂ) * G j (f x)


/-- The chain rule in weak form: for `v ∈ H¹(f(Ω))` with weak gradient `G` and a test function
`θ` on `Ω`, `∫_Ω (v ∘ f) ∂_i θ = -∫_Ω (∑_j (∂_i f)_j (G_j ∘ f)) θ`. -/
theorem integral_comp_mul_fderiv_bilip (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) {v : L2 (f '' Ω)} {G : Fin 2 → L2 (f '' Ω)}
    (hG : IsWeakGradient (f '' Ω) v G) {θ : ℂ → ℂ} (hθ : TestFunction Ω θ) (i : Fin 2) :
    ∫ x in Ω, v (f x) * fderiv ℝ θ x (coordDir i) =
      -∫ x in Ω, chainGrad f (fun j => G j) i x * θ x := by
  have hΩ'  := f.isOpenMap Ω hΩ
  set V := extZero (f '' Ω) v
  set Gx : Fin 2 → ℂ → ℂ := fun j => extZero (f '' Ω) (G j)
  have hV  := memLp_extZero hΩ'.measurableSet v
  have hGx  := fun j => memLp_extZero hΩ'.measurableSet (G j)
  set r : ℕ → ℝ := fun k => 1 / (k + 1)
  have hr : ∀ k, 0 < r k := fun k => by positivity
  set φ : ℕ → ContDiffBump (0 : ℂ) := fun k => ⟨r k / 2, r k, by positivity, by simp_all⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set ψ : ℕ → ℂ → ℂ := fun k => mollify ((φ k).normed volume) V
  have hψ1 : ∀ k, ContDiff ℝ 1 (ψ k) := fun k =>
    HasCompactSupport.contDiff_convolution_left _ ((φ k).hasCompactSupport_normed)
      ((φ k).contDiff_normed) (hV.locallyIntegrable one_le_two)
  obtain ⟨hθc, hθs, hθΩ⟩ := hθ
  set c : Fin 2 → ℂ → ℂ := fun j x => coordRe j (fderiv ℝ f x (coordDir i)) * θ x
  have hc : ∀ j, MemLp (c j) 2 (volume.restrict Ω) := by
    intro j
    refine ((hθc.continuous.memLp_of_hasCompactSupport hθs).restrict _).of_le_mul (c := K) ?_ ?_
    · exact (Complex.measurable_ofReal.comp (measurable_coordRe_fderiv f i j)).aestronglyMeasurable.mul
        hθc.continuous.aestronglyMeasurable
    · rw [ae_restrict_iff' hΩ.measurableSet]
      refine Eventually.of_forall fun x hx => ?_
      rw [norm_mul, Complex.norm_real]
      gcongr
      refine (abs_coordRe_le j _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
      rw [norm_coordDir, mul_one]
      exact norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hx) hf
  have hInt : ∀ {H : ℂ → ℂ}, MemLp H 2 volume → ∀ j,
      Integrable (fun x => H (f x) * c j x) (volume.restrict Ω) := fun hH j =>
    (memLp_comp_bilip' hΩ hK hf hg (hH.restrict _)).integrable_mul (hc j)
  -- uniform interior margin
  obtain ⟨δ, hδ, hδsub⟩ := (hθs.isCompact.image f.continuous).exists_cthickening_subset_open hΩ'
    (image_mono hθΩ)
  have hball : ∀ᶠ k in atTop, ∀ x ∈ tsupport θ, closedBall (f x) (φ k).rOut ⊆ f '' Ω := by
    filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with k hk x hx
    exact (closedBall_subset_closedBall hk.le).trans
      ((closedBall_subset_cthickening (mem_image_of_mem f hx) δ).trans hδsub)
  -- the identity for the mollified functions
  have hk_eq  := fun k =>
    setIntegral_comp_mul_fderiv hΩ hf (hψ1 k) ⟨hθc, hθs, hθΩ⟩ (coordDir i)
  have hk_sum : ∀ᶠ k in atTop, ∫ x in Ω, fderiv ℝ (ψ k) (f x) (fderiv ℝ f x (coordDir i)) * θ x =
      ∑ j, ∫ x in Ω, mollify ((φ k).normed volume) (Gx j) (f x) * c j x := by
    filter_upwards [hball] with k hk
    rw [← integral_finset_sum _ (fun j _ => hInt (memLp_mollify (φ k) (hGx j)) j)]
    refine setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
    by_cases hxt : x ∈ tsupport θ
    · rw [clm_apply_eq_sum_coordRe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [fderiv_mollify_extZero hΩ' hG (φ k) (f x) (hk x hxt) j]
      ring
    simp [c, image_eq_zero_of_notMem_tsupport hxt]
  -- limits
  have hL := tendsto_setIntegral_comp_mul hΩ hK hf hg (fun k => memLp_mollify (φ k) hV) hV
    (tendsto_mollify_L2 hφ hV) ((((hθc.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hθs.fderiv ℝ).comp_left (g := fun T  => T (coordDir i)) (by simp))).restrict _)
  have e1 : ∫ x in Ω, V (f x) * fderiv ℝ θ x (coordDir i) =
      ∫ x in Ω, v (f x) * fderiv ℝ θ x (coordDir i) :=
    setIntegral_congr_fun hΩ.measurableSet fun x hx => by
      simp [V, extZero, mem_image_of_mem f hx]
  have e2 : ∑ j, ∫ x in Ω, Gx j (f x) * c j x =
      ∫ x in Ω, chainGrad f (fun j => G j) i x * θ x := by
    rw [← integral_finset_sum _ (fun j _ => hInt (hGx j) j)]
    refine setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
    simp only [chainGrad, extZero, indicator_of_mem (mem_image_of_mem f hx), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [← e1, tendsto_nhds_unique hL ((tendsto_finset_sum _ fun j _ => tendsto_setIntegral_comp_mul hΩ hK hf hg
      (fun k => memLp_mollify (φ k) (hGx j)) (hGx j) (tendsto_mollify_L2 hφ (hGx j)) (hc j)).neg.congr' (by
    filter_upwards [hk_sum] with k hk
    rw [hk_eq k, hk])), e2]


lemma memLp_chainGrad (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) (G : Fin 2 → L2 (f '' Ω)) (i : Fin 2) :
    MemLp (chainGrad f (fun j => G j) i) 2 (volume.restrict Ω) := by
  have : chainGrad f (fun j => G j) i =
      ∑ j, fun x => coordRe j (fderiv ℝ f x (coordDir i)) * G j (f x) := by
    rfl
  rw [this]
  refine memLp_finset_sum' _ fun j _ => ?_
  refine (memLp_comp_bilip hΩ hK hf hg (G j)).of_le_mul (c := K) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_coordRe_fderiv f i j)).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (G j)).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_restrict hg))
  · rw [ae_restrict_iff' hΩ.measurableSet]
    refine Eventually.of_forall fun x hx => ?_
    rw [norm_mul, Complex.norm_real]
    gcongr
    refine (abs_coordRe_le j _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    rw [norm_coordDir, mul_one]
    exact norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hx) hf

/-- **The Sobolev chain rule for bi-Lipschitz maps.** If `v ∈ H¹(f(Ω))` has weak gradient `G`
and `u = v ∘ f` a.e. on `Ω`, then `u` has weak gradient `∂_i u = ∑_j (∂_i f)_j (G_j ∘ f)`. -/
theorem isWeakGradient_comp_bilip (hΩ : IsOpen Ω) (hK : 0 < K) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) {v : L2 (f '' Ω)} {G : Fin 2 → L2 (f '' Ω)}
    (hG : IsWeakGradient (f '' Ω) v G) {u : L2 Ω}
    (hu : u =ᵐ[volume.restrict Ω] fun x => v (f x)) :
    IsWeakGradient Ω u (fun i => (memLp_chainGrad hΩ hK hf hg G i).toLp _) := by
  intro θ hθ i
  have e : ∫ x in Ω, u x * fderiv ℝ θ x (coordDir i) =
      ∫ x in Ω, v (f x) * fderiv ℝ θ x (coordDir i) :=
    integral_congr_ae (hu.mono fun x hx => by simp_all)
  rw [e, integral_comp_mul_fderiv_bilip hΩ hK hf hg hG hθ i]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(memLp_chainGrad hΩ hK hf hg G i).coeFn_toLp] with x hx
  simp_all

/-- The chain rule, with the image `f(Ω) = V` given as a separate set. -/
theorem exists_isWeakGradient_comp_bilip {V : Set ℂ} (hV : f '' Ω = V) (hΩ : IsOpen Ω)
    (hK : 0 < K) (hf : LipschitzOnWith K f Ω) (hg : LipschitzOnWith K f.symm V) {v : L2 V}
    {G : Fin 2 → L2 V} (hG : IsWeakGradient V v G) {u : L2 Ω}
    (hu : u =ᵐ[volume.restrict Ω] fun x => v (f x)) :
    ∃ g : Fin 2 → L2 Ω, IsWeakGradient Ω u g ∧
      ∀ i, g i =ᵐ[volume.restrict Ω] chainGrad f (fun j => G j) i := by
  subst hV
  exact ⟨_, isWeakGradient_comp_bilip hΩ hK hf hg hG hu,
    fun i => (memLp_chainGrad hΩ hK hf hg G i).coeFn_toLp⟩

end ChainRule

end PolyaNeumann

end
