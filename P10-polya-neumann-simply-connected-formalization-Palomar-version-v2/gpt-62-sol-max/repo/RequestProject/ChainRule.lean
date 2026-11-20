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

/-! ### Integration by parts for Lipschitz functions -/

/-- Integration by parts for a real Lipschitz function against a `C¹` compactly supported function
(from Rademacher's theorem). -/
lemma integral_fderiv_mul_real {C : ℝ≥0} {F θ : ℂ → ℝ} (hF : LipschitzWith C F)
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
    have hx := (hθ.differentiable one_ne_zero) x
    grind [hx.lineDeriv_eq_fderiv, map_neg]
  simp_all

/-- Integration by parts for a complex Lipschitz function against a `C¹` compactly supported
function: `∫ F ∂_e θ = -∫ (∂_e F) θ`, with `∂_e F` the a.e. defined derivative. -/
lemma integral_mul_fderiv_of_lipschitz {C : ℝ≥0} {F θ : ℂ → ℂ} (hF : LipschitzWith C F)
    (hθ : ContDiff ℝ 1 θ) (hθs : HasCompactSupport θ) (e : ℂ) :
    ∫ x, F x * fderiv ℝ θ x e = -∫ x, fderiv ℝ F x e * θ x := by
  let Df (x : ℂ) := fderiv ℝ F x e
  let Dt (x : ℂ) := fderiv ℝ θ x e
  have hDt : Continuous Dt := (hθ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsDt : HasCompactSupport Dt :=
    (hθs.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℂ => T e) (by simp)
  have hDf (x : ℂ) : ‖Df x‖ ≤ C * ‖e‖ := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg _))
  have iL {A : Type} [NormedRing A] [NormedSpace ℝ A] (r s : ℂ →L[ℝ] A) :
      Integrable (fun x => r (F x) * s (Dt x)) :=
    ((r.continuous.comp hF.continuous).mul (s.continuous.comp hDt)).integrable_of_hasCompactSupport
      (hsDt.comp_left s.map_zero).mul_left
  have iR {A : Type} [NormedRing A] [NormedSpace ℝ A] (r s : ℂ →L[ℝ] A) :
      Integrable (fun x => r (Df x) * s (θ x)) :=
    ((s.continuous.comp hθ.continuous).integrable_of_hasCompactSupport (hθs.comp_left s.map_zero)).bdd_mul
      (r.continuous.comp_aestronglyMeasurable (measurable_fderiv_apply_const ℝ F e).aestronglyMeasurable)
      (Eventually.of_forall fun x => (r.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hDf x) (norm_nonneg _)))
  have ibp (r s : ℂ →L[ℝ] ℝ) : (∫ x, r (F x) * s (Dt x)) = -(∫ x, r (Df x) * s (θ x)) := by
    have h := integral_fderiv_mul_real (r.lipschitz.comp hF) (s.contDiff.comp hθ)
      (hθs.comp_left s.map_zero) e
    have hdF : ∀ᵐ x, fderiv ℝ (r ∘ F) x e = r (Df x) := by
      filter_upwards [hF.ae_differentiableAt] with x hx
      rw [(r.hasFDerivAt.comp x hx.hasFDerivAt).fderiv]
      rfl
    have hdθ (x : ℂ) : fderiv ℝ (s ∘ θ) x e = s (Dt x) := by
      rw [(s.hasFDerivAt.comp x (hθ.differentiable one_ne_zero x).hasFDerivAt).fderiv]
      rfl
    rw [integral_congr_ae (hdF.mono fun x hx => by rw [hx])] at h
    simp only [Function.comp_apply, hdθ] at h
    linear_combination h
  have I1 : Integrable (fun x => F x * Dt x) := iL (ContinuousLinearMap.id ℝ ℂ) (ContinuousLinearMap.id ℝ ℂ)
  have I2 : Integrable (fun x => Df x * θ x) := iR (ContinuousLinearMap.id ℝ ℂ) (ContinuousLinearMap.id ℝ ℂ)
  let r := Complex.reCLM
  let s := Complex.imCLM
  apply Complex.ext
  · change (∫ x, F x * Dt x).re = (-(∫ x, Df x * θ x)).re
    rw [Complex.neg_re]
    change r (∫ x, F x * Dt x) = -r (∫ x, Df x * θ x)
    rw [← r.integral_comp_comm I1, ← r.integral_comp_comm I2]
    change (∫ x, (F x * Dt x).re) = -(∫ x, (Df x * θ x).re)
    simp_rw [Complex.mul_re]
    erw [integral_sub (iL r r) (iL s s), integral_sub (iR r r) (iR s s), ibp r r, ibp s s]
    ring
  · change (∫ x, F x * Dt x).im = (-(∫ x, Df x * θ x)).im
    rw [Complex.neg_im]
    change s (∫ x, F x * Dt x) = -s (∫ x, Df x * θ x)
    rw [← s.integral_comp_comm I1, ← s.integral_comp_comm I2]
    change (∫ x, (F x * Dt x).im) = -(∫ x, (Df x * θ x).im)
    simp_rw [Complex.mul_im]
    erw [integral_add (iL r s) (iL s r), integral_add (iR r s) (iR s r), ibp r s, ibp s r]
    ring

/-- The chain rule `∂_e (ψ ∘ f) = Dψ(f) (∂_e f)` for a `C¹` function `ψ` and a map `f` which is
Lipschitz on an open set `U`, in weak form against test functions on `U`. -/
lemma setIntegral_comp_mul_fderiv {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f U) {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) {θ : ℂ → ℂ}
    (hθ : TestFunction U θ) (e : ℂ) :
    ∫ x in U, ψ (f x) * fderiv ℝ θ x e =
      -∫ x in U, fderiv ℝ ψ (f x) (fderiv ℝ f x e) * θ x := by
  obtain ⟨hθc, hθs, hθU⟩ := hθ
  have hθ1 : ContDiff ℝ 1 θ := hθc.of_le (by norm_num)
  obtain ⟨R, hR⟩ := hθs.isCompact.isBounded.subset_ball 0
  obtain ⟨f', hf', hff'⟩ := hf.extend_finite_dimension
  obtain ⟨R', hR'⟩ := (hf'.isBounded_image (isBounded_ball (x := (0 : ℂ)) (r := R))).subset_closedBall 0
  obtain ⟨Kψ, hKψ⟩ := (hψ.contDiffOn (s := closedBall (0 : ℂ) R')).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall 0 R') (isCompact_closedBall 0 R')
  have hcomp :=
    hKψ.comp (hf'.lipschitzOnWith) (fun x hx => hR' (mem_image_of_mem f' hx))
  obtain ⟨F, hF, hFeq⟩ := hcomp.extend_finite_dimension
  set W := U ∩ ball (0 : ℂ) R
  have hW : IsOpen W := hU.inter isOpen_ball
  have hKW := subset_inter hθU hR
  have hFW : ∀ x ∈ W, F x = ψ (f x) := fun x hx => by grind
  have hIBP := integral_mul_fderiv_of_lipschitz hF hθ1 hθs e
  have hdθ0 : ∀ x ∉ tsupport θ, fderiv ℝ θ x e = 0 := fun x hx => by
    rw [show fderiv ℝ θ x = 0 from Function.notMem_support.mp
      (fun h => hx (support_fderiv_subset ℝ h))]
    rfl
  have hθ0 : ∀ x ∉ tsupport θ, θ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have L : ∫ x in U, ψ (f x) * fderiv ℝ θ x e = ∫ x, F x * fderiv ℝ θ x e := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    grind
    grind
  have Rr : ∫ x in U, fderiv ℝ ψ (f x) (fderiv ℝ f x e) * θ x = ∫ x, fderiv ℝ F x e * θ x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (f := fun x => fderiv ℝ F x e * θ x)
      (fun x hx => by grind)]
    refine setIntegral_congr_ae hU.measurableSet ?_
    have hd := ae_differentiableAt_of_lipschitzOnWith hU hf
    rw [ae_restrict_iff' hU.measurableSet] at hd
    filter_upwards [hd] with x hdx hxU
    by_cases hx : x ∈ tsupport θ
    · have hev : F =ᶠ[𝓝 x] ψ ∘ f :=
        Filter.eventually_of_mem (hW.mem_nhds (hKW hx)) fun y hy => hFW y hy
      rw [hev.fderiv_eq, fderiv_comp x ((hψ.differentiable one_ne_zero) _) (hdx hxU)]
      rfl
    simp_all
  simp_all

/-! ### Composition with a bi-Lipschitz map in `L²` -/

section BiLip

variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : ℝ≥0}

/-- If `W_k → W` in `L²(ℂ)`, then `∫_Ω (W_k ∘ f) c → ∫_Ω (W ∘ f) c` for `c ∈ L²(Ω)`. -/
lemma tendsto_setIntegral_comp_mul (hg : LipschitzOnWith K f.symm (f '' Ω)) {W : ℕ → ℂ → ℂ} {W₀ : ℂ → ℂ}
    (hW : ∀ k, MemLp (W k) 2 volume) (hW₀ : MemLp W₀ 2 volume)
    (hconv : Tendsto (fun k => eLpNorm (W k - W₀) 2 volume) atTop (𝓝 0)) {c : ℂ → ℂ}
    (hc : MemLp c 2 (volume.restrict Ω)) :
    Tendsto (fun k => ∫ x in Ω, W k (f x) * c x) atTop (𝓝 (∫ x in Ω, W₀ (f x) * c x)) := by
  have hm : ∀ {H : ℂ → ℂ}, MemLp H 2 volume → MemLp (fun x => H (f x)) 2 (volume.restrict Ω) :=
    fun hH => memLp_comp_bilip hg (hH.restrict _)
  have hint : ∀ {H : ℂ → ℂ}, MemLp H 2 volume →
      Integrable (fun x => H (f x) * c x) (volume.restrict Ω) :=
    fun hH => (hm hH).integrable_mul hc
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ k, ‖(∫ x in Ω, W k (f x) * c x) - ∫ x in Ω, W₀ (f x) * c x‖ ≤
      ((K : ℝ≥0∞) * eLpNorm (W k - W₀) 2 volume).toReal * (eLpNorm c 2 (volume.restrict Ω)).toReal := by
    intro k
    rw [← integral_sub (hint (hW k)) (hint hW₀)]
    have e : (fun x => W k (f x) * c x - W₀ (f x) * c x) = fun x => (W k - W₀) (f x) * c x := by
      simp [sub_mul]
    rw [e]
    refine (norm_integral_mul_le_eLpNorm (hm ((hW k).sub hW₀)) hc).trans ?_
    gcongr
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ((hW k).sub hW₀).eLpNorm_ne_top
    · exact (eLpNorm_comp_bilip_le hg _).trans
        (mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _)
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  have : Tendsto (fun k => ((K : ℝ≥0∞) * eLpNorm (W k - W₀) 2 volume).toReal) atTop (𝓝 0) := by
    rw [← ENNReal.toReal_zero]
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
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul]
  aesop

lemma abs_coordRe_le (j : Fin 2) (w : ℂ) : |coordRe j w| ≤ ‖w‖ := by
  fin_cases j
  exact Complex.abs_re_le_norm w
  exact Complex.abs_im_le_norm w

lemma norm_coordDir (i : Fin 2) : ‖coordDir i‖ = 1 := by
  fin_cases i <;> simp [coordDir]

lemma measurable_coordRe_fderiv (f : ℂ → ℂ) (i j : Fin 2) :
    Measurable fun x => coordRe j (fderiv ℝ f x (coordDir i)) := by
  fin_cases j
  exact Complex.measurable_re.comp (measurable_fderiv_apply_const ℝ f _)
  exact Complex.measurable_im.comp (measurable_fderiv_apply_const ℝ f _)

lemma memLp_mollify (φ : ContDiffBump (0 : ℂ)) {H : ℂ → ℂ} (hH : MemLp H 2 volume) :
    MemLp (mollify (φ.normed volume) H) 2 volume :=
  ((eLpNorm_mollify_le φ hH.aestronglyMeasurable).trans_lt hH.eLpNorm_lt_top)

/-- The chain rule gradient `∂_i (v ∘ f) = ∑_j (∂_i f)_j (G_j ∘ f)`. -/
def chainGrad (f : ℂ → ℂ) (G : Fin 2 → ℂ → ℂ) (i : Fin 2) (x : ℂ) : ℂ :=
  ∑ j, (coordRe j (fderiv ℝ f x (coordDir i)) : ℂ) * G j (f x)


/-- The chain rule in weak form: for `v ∈ H¹(f(Ω))` with weak gradient `G` and a test function
`θ` on `Ω`, `∫_Ω (v ∘ f) ∂_i θ = -∫_Ω (∑_j (∂_i f)_j (G_j ∘ f)) θ`. -/
theorem integral_comp_mul_fderiv_bilip (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω)
    (hg : LipschitzOnWith K f.symm (f '' Ω)) {v : L2 (f '' Ω)} {G : Fin 2 → L2 (f '' Ω)}
    (hG : IsWeakGradient (f '' Ω) v G) {θ : ℂ → ℂ} (hθ : TestFunction Ω θ) (i : Fin 2) :
    ∫ x in Ω, (v : ℂ → ℂ) (f x) * fderiv ℝ θ x (coordDir i) =
      -∫ x in Ω, chainGrad f (fun j => (G j : ℂ → ℂ)) i x * θ x := by
  have hΩ' := f.isOpenMap Ω hΩ
  set V := extZero (f '' Ω) v
  set Gx : Fin 2 → ℂ → ℂ := fun j => extZero (f '' Ω) (G j)
  have hV := memLp_extZero hΩ'.measurableSet v
  have hGx := fun j => memLp_extZero hΩ'.measurableSet (G j)
  set r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hr : ∀ k, 0 < r k := fun k => by positivity
  set φ : ℕ → ContDiffBump (0 : ℂ) := fun k => ⟨r k / 2, r k, by positivity, by simp_all⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set ψ : ℕ → ℂ → ℂ := fun k => mollify ((φ k).normed volume) V
  have hψ1 : ∀ k, ContDiff ℝ 1 (ψ k) := fun k =>
    HasCompactSupport.contDiff_convolution_left _ ((φ k).hasCompactSupport_normed)
      ((φ k).contDiff_normed) (hV.locallyIntegrable one_le_two)
  obtain ⟨hθc, hθs, hθΩ⟩ := hθ
  have hθm : MemLp θ 2 (volume.restrict Ω) :=
    (hθc.continuous.memLp_of_hasCompactSupport hθs).restrict _
  -- the coefficients `c_j = (∂_i f)_j θ`
  set c : Fin 2 → ℂ → ℂ := fun j x => (coordRe j (fderiv ℝ f x (coordDir i)) : ℂ) * θ x
  have hc : ∀ j, MemLp (c j) 2 (volume.restrict Ω) := by
    intro j
    refine hθm.of_le_mul (c := K) ?_ ?_
    · exact (Complex.measurable_ofReal.comp (measurable_coordRe_fderiv f i j)).aestronglyMeasurable.mul
        hθc.continuous.aestronglyMeasurable
    · rw [ae_restrict_iff' hΩ.measurableSet]
      refine Eventually.of_forall fun x hx => ?_
      rw [norm_mul, Complex.norm_real]
      gcongr
      refine (abs_coordRe_le j _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
      rw [norm_coordDir, mul_one]
      exact norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hx) hf
  have hdθ : MemLp (fun x => fderiv ℝ θ x (coordDir i)) 2 (volume.restrict Ω) :=
    (((hθc.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hθs.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℂ => T (coordDir i)) (by simp))).restrict _
  have hInt : ∀ {H : ℂ → ℂ}, MemLp H 2 volume → ∀ j,
      Integrable (fun x => H (f x) * c j x) (volume.restrict Ω) := fun hH j =>
    (memLp_comp_bilip hg (hH.restrict _)).integrable_mul (hc j)
  -- uniform interior margin
  obtain ⟨δ, hδ, hδsub⟩ := (hθs.isCompact.image f.continuous).exists_cthickening_subset_open hΩ'
    (image_mono hθΩ)
  have hball : ∀ᶠ k in atTop, ∀ x ∈ tsupport θ, closedBall (f x) (φ k).rOut ⊆ f '' Ω := by
    filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with k hk x hx
    exact (closedBall_subset_closedBall hk.le).trans
      ((closedBall_subset_cthickening (mem_image_of_mem f hx) δ).trans hδsub)
  -- the identity for the mollified functions
  have hk_eq := fun k =>
    setIntegral_comp_mul_fderiv hΩ hf (hψ1 k) ⟨hθc, hθs, hθΩ⟩ (coordDir i)
  have hk_sum : ∀ᶠ k in atTop, ∫ x in Ω, fderiv ℝ (ψ k) (f x) (fderiv ℝ f x (coordDir i)) * θ x =
      ∑ j, ∫ x in Ω, mollify ((φ k).normed volume) (Gx j) (f x) * c j x := by
    filter_upwards [hball] with k hk
    rw [← integral_finset_sum _ (fun j _ => hInt (memLp_mollify (φ k) (hGx j)) j)]
    refine setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
    by_cases hxt : x ∈ tsupport θ
    · simp only [c]
      rw [clm_apply_eq_sum_coordRe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [fderiv_mollify_extZero hΩ' hG (φ k) (f x) (hk x hxt) j]
      ring
    · simp [c, image_eq_zero_of_notMem_tsupport hxt]
  -- limits
  have hL := tendsto_setIntegral_comp_mul hg (fun k => memLp_mollify (φ k) hV) hV
    (tendsto_mollify_L2 hφ hV) hdθ
  have hR : Tendsto (fun k => ∑ j, ∫ x in Ω, mollify ((φ k).normed volume) (Gx j) (f x) * c j x)
      atTop (𝓝 (∑ j, ∫ x in Ω, Gx j (f x) * c j x)) :=
    tendsto_finset_sum _ fun j _ => tendsto_setIntegral_comp_mul hg
      (fun k => memLp_mollify (φ k) (hGx j)) (hGx j) (tendsto_mollify_L2 hφ (hGx j)) (hc j)
  have hlim := tendsto_nhds_unique hL (hR.neg.congr' (by
    filter_upwards [hk_sum] with k hk
    rw [hk_eq k, hk]))
  have e1 : ∫ x in Ω, V (f x) * fderiv ℝ θ x (coordDir i) =
      ∫ x in Ω, (v : ℂ → ℂ) (f x) * fderiv ℝ θ x (coordDir i) :=
    setIntegral_congr_fun hΩ.measurableSet fun x hx => by
      simp [V, extZero, mem_image_of_mem f hx]
  have e2 : ∑ j, ∫ x in Ω, Gx j (f x) * c j x =
      ∫ x in Ω, chainGrad f (fun j => (G j : ℂ → ℂ)) i x * θ x := by
    rw [← integral_finset_sum _ (fun j _ => hInt (hGx j) j)]
    refine setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
    simp only [chainGrad, extZero, indicator_of_mem (mem_image_of_mem f hx), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [← e1, hlim, e2]


section

variable (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω) (hg : LipschitzOnWith K f.symm (f '' Ω))
include hΩ hf hg

lemma memLp_chainGrad  (G : Fin 2 → L2 (f '' Ω)) (i : Fin 2) :
    MemLp (chainGrad f (fun j => (G j : ℂ → ℂ)) i) 2 (volume.restrict Ω) := by
  have : chainGrad f (fun j => (G j : ℂ → ℂ)) i =
      ∑ j, fun x => (coordRe j (fderiv ℝ f x (coordDir i)) : ℂ) * (G j : ℂ → ℂ) (f x) := by
    rfl
  rw [this]
  refine memLp_finset_sum' _ fun j _ => ?_
  refine (memLp_comp_bilip hg (Lp.memLp (G j))).of_le_mul (c := K) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_coordRe_fderiv f i j)).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (G j)).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_restrict hg))
  · rw [ae_restrict_iff' hΩ.measurableSet]
    refine Eventually.of_forall fun x hx => ?_
    simp only [norm_mul, Complex.norm_real, Function.comp_apply]
    gcongr
    refine (abs_coordRe_le j _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    rw [norm_coordDir, mul_one]
    exact norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hx) hf

/-- **The Sobolev chain rule for bi-Lipschitz maps.** If `v ∈ H¹(f(Ω))` has weak gradient `G`
and `u = v ∘ f` a.e. on `Ω`, then `u` has weak gradient `∂_i u = ∑_j (∂_i f)_j (G_j ∘ f)`. -/
theorem isWeakGradient_comp_bilip  {v : L2 (f '' Ω)} {G : Fin 2 → L2 (f '' Ω)}
    (hG : IsWeakGradient (f '' Ω) v G) {u : L2 Ω}
    (hu : (u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun x => (v : ℂ → ℂ) (f x)) :
    IsWeakGradient Ω u (fun i => (memLp_chainGrad hΩ hf hg G i).toLp _) := by
  intro θ hθ i
  have e : ∫ x in Ω, (u : ℂ → ℂ) x * fderiv ℝ θ x (coordDir i) =
      ∫ x in Ω, (v : ℂ → ℂ) (f x) * fderiv ℝ θ x (coordDir i) :=
    integral_congr_ae (hu.mono fun x hx => by tauto)
  rw [e, integral_comp_mul_fderiv_bilip hΩ hf hg hG hθ i]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(memLp_chainGrad hΩ hf hg G i).coeFn_toLp] with x hx
  tauto

end

/-- The chain rule, with the image `f(Ω) = V` given as a separate set. -/
theorem exists_isWeakGradient_comp_bilip {V : Set ℂ} (hV : f '' Ω = V) (hΩ : IsOpen Ω)
    (hf : LipschitzOnWith K f Ω) (hg : LipschitzOnWith K f.symm V) {v : L2 V}
    {G : Fin 2 → L2 V} (hG : IsWeakGradient V v G) {u : L2 Ω}
    (hu : (u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun x => (v : ℂ → ℂ) (f x)) :
    ∃ g : Fin 2 → L2 Ω, IsWeakGradient Ω u g ∧
      ∀ i, (g i : ℂ → ℂ) =ᵐ[volume.restrict Ω] chainGrad f (fun j => (G j : ℂ → ℂ)) i := by
  subst hV
  exact ⟨_, isWeakGradient_comp_bilip hΩ hf hg hG hu,
    fun i => (memLp_chainGrad hΩ hf hg G i).coeFn_toLp⟩

end ChainRule

end PolyaNeumann

end
