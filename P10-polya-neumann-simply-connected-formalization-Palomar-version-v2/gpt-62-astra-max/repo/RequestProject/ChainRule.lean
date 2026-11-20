module

public import RequestProject.L2Identities

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

/-- The weak gradient identity tested against the reflected bump `t ↦ ρ(x - t)`. -/
lemma integral_fderiv_bump_smul_eq {Ω : Set ℂ} (hΩ : IsOpen Ω) {v : L2 Ω} {G : Fin 2 → L2 Ω}
    (hG : IsWeakGradient Ω v G) (φ : ContDiffBump (0 : ℂ)) (x : ℂ)
    (hx : closedBall x φ.rOut ⊆ Ω) (i : Fin 2) :
    ∫ t, fderiv ℝ (φ.normed volume) (x - t) (coordDir i) • extZero Ω v t =
      ∫ t, φ.normed volume (x - t) • extZero Ω (G i) t := by
  have h := hG (reflBump φ x) (testFunction_reflBump φ x hx) i
  simp_rw [fderiv_reflBump] at h
  have e1 : ∀ t, fderiv ℝ (φ.normed volume) (x - t) (coordDir i) • extZero Ω v t =
      Ω.indicator (fun t => -((v : ℂ → ℂ) t *
        -((fderiv ℝ (φ.normed volume) (x - t) (coordDir i) : ℝ) : ℂ))) t := by
    intro t
    by_cases ht : t ∈ Ω
    · simp [extZero, ht, Complex.real_smul, mul_comm]
    · simp [extZero, ht]
  have e2 : ∀ t, φ.normed volume (x - t) • extZero Ω (G i) t =
      Ω.indicator (fun t => (G i : ℂ → ℂ) t * reflBump φ x t) t := by
    intro t
    by_cases ht : t ∈ Ω
    · simp [extZero, reflBump, ht, Complex.real_smul, mul_comm]
    · simp [extZero, ht]
  simp_rw [e1, e2]
  rw [integral_indicator hΩ.measurableSet, integral_indicator hΩ.measurableSet, integral_neg, h,
    neg_neg]

/-- The mollification of an `H¹` function is differentiated by mollifying its weak gradient. -/
lemma fderiv_mollify_extZero {Ω : Set ℂ} (hΩ : IsOpen Ω) {v : L2 Ω} {G : Fin 2 → L2 Ω}
    (hG : IsWeakGradient Ω v G) (φ : ContDiffBump (0 : ℂ)) (x : ℂ)
    (hx : closedBall x φ.rOut ⊆ Ω) (i : Fin 2) :
    fderiv ℝ (mollify (φ.normed volume) (extZero Ω v)) x (coordDir i) =
      mollify (φ.normed volume) (extZero Ω (G i)) x := by
  have hV : LocallyIntegrable (extZero Ω v) volume :=
    locallyIntegrable_indicator_L2 hΩ.measurableSet v
  have hd := HasCompactSupport.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.hasCompactSupport_normed (μ := volume)) (φ.contDiff_normed (n := 1)) hV x
  have hint := HasCompactSupport.convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
    ((φ.hasCompactSupport_normed (μ := volume)).fderiv ℝ)
    ((φ.contDiff_normed (n := 1)).continuous_fderiv (by simp)) hV x
  unfold mollify
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  rw [← integral_sub_left_eq_self _ volume x]
  simp only [sub_sub_cancel]
  rw [integral_fderiv_bump_smul_eq hΩ hG φ x hx i, convolution_def,
    ← integral_sub_left_eq_self _ volume x]
  simp

/-! ### Integration by parts for Lipschitz functions -/

/-- The product of two Lipschitz fields is Lipschitz if one factor has compact
support. In the cross term it suffices to bound the other factor on that support. -/
private lemma lipschitz_mul_compact {F g : ℂ → ℂ} {C D : ℝ≥0} (hF : LipschitzWith C F)
    (hg : LipschitzWith D g) (hs : HasCompactSupport g) : ∃ L, LipschitzWith L (F * g) := by
  obtain ⟨A, hA⟩ := hs.isCompact.exists_bound_of_continuousOn hF.continuous.continuousOn
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hg.continuous
  let L := A.toNNReal * D + C * B.toNNReal
  have hxy (x y : ℂ) (hx : x ∈ tsupport g) : dist ((F*g) x) ((F*g) y) ≤ L * dist x y := by
    rw [dist_eq_norm, Pi.mul_apply, Pi.mul_apply]
    calc _ = ‖F x * (g x - g y) + (F x - F y) * g y‖ := by ring_nf
         _ ≤ _ := norm_add_le ..
         _ = _ := by rw [norm_mul, norm_mul]
         _ ≤ (A.toNNReal : ℝ) * (D * dist x y) + (C * dist x y) * B.toNNReal := by
           gcongr
           · exact (hA x hx).trans (Real.le_coe_toNNReal _)
           · simpa only [← dist_eq_norm] using hg.dist_le_mul x y
           · simpa only [← dist_eq_norm] using hF.dist_le_mul x y
           · exact (hB y).trans (Real.le_coe_toNNReal _)
         _ = _ := by simp [L]; ring
  refine ⟨L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact hxy x y hx
  by_cases hy : y ∈ tsupport g
  · simpa only [dist_comm] using hxy y x hy
  simp [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]; positivity

/-- Test the derivative against the constant `1`. Real scalar projections
commute with integration and with the derivative at differentiability points. -/
private lemma integral_fderiv_lip_compact {f : ℂ → ℂ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hs : HasCompactSupport f) (e : ℂ) (hi : Integrable fun x => fderiv ℝ f x e) :
    ∫ x, fderiv ℝ f x e = 0 := by
  have H (L : ℂ →L[ℝ] ℝ) : L (∫ x, fderiv ℝ f x e) = 0 := by
    rw [← L.integral_comp_comm hi]
    have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume) (LipschitzWith.const (1 : ℝ))
      (L.lipschitzWith.comp hf) (hs.comp_left (g := L) L.map_zero) (-e)
    have hc (x : ℂ) : lineDeriv ℝ (fun _ : ℂ => (1:ℝ)) x (-e) = 0 := by simp [lineDeriv]
    simp only [hc, zero_mul, integral_zero, neg_neg, mul_one] at h
    refine (integral_congr_ae ?_).trans h.symm
    filter_upwards [hf.ae_differentiableAt] with x hx
    rw [((L.differentiableAt).comp x hx).lineDeriv_eq_fderiv, fderiv_comp x L.differentiableAt hx, L.fderiv]
    rfl
  exact Complex.ext (H Complex.reCLM) (H Complex.imCLM)

/-- Integration by parts for a complex Lipschitz function against a `C¹` compactly supported
function: `∫ F ∂_e θ = -∫ (∂_e F) θ`, with `∂_e F` the a.e. defined derivative. -/
lemma integral_mul_fderiv_of_lipschitz {C : ℝ≥0} {F θ : ℂ → ℂ} (hF : LipschitzWith C F)
    (hθ : ContDiff ℝ 1 θ) (hθs : HasCompactSupport θ) (e : ℂ) :
    ∫ x, F x * fderiv ℝ θ x e = -∫ x, fderiv ℝ F x e * θ x := by
  have I1 : Integrable fun x => F x * fderiv ℝ θ x e := by
    refine (hF.continuous.mul ((by fun_prop))).integrable_of_hasCompactSupport ?_
    exact ((hθs.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℂ => T e) (by simp)).mul_left
  have I2 : Integrable fun x => fderiv ℝ F x e * θ x := by
    refine (hθ.continuous.integrable_of_hasCompactSupport hθs).bdd_mul (c := C * ‖e‖)
      (by fun_prop)
      (Eventually.of_forall fun x => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg _))
  obtain ⟨D, hD⟩ := hθ.lipschitzWith_of_hasCompactSupport hθs (by norm_num)
  obtain ⟨L, hL⟩ := lipschitz_mul_compact hF hD hθs
  have he : (fun x => F x * fderiv ℝ θ x e + fderiv ℝ F x e * θ x) =ᵐ[volume]
      fun x => fderiv ℝ (F*θ) x e := by
    filter_upwards [hF.ae_differentiableAt] with x hx
    rw [fderiv_mul hx (hθ.differentiable one_ne_zero x)]
    simp [mul_comm]
  rw [← add_eq_zero_iff_eq_neg, ← integral_add I1 I2, integral_congr_ae he]
  exact integral_fderiv_lip_compact hL hθs.mul_left e ((I1.add I2).congr he)

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
  obtain ⟨R', hR'⟩ := (hf'.isBounded_image (isBounded_ball  (r := R))).subset_closedBall 0
  obtain ⟨Kψ, hKψ⟩ := hψ.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall 0 R') (isCompact_closedBall 0 R')
  
  obtain ⟨F, hF, hFeq⟩ := (hKψ.comp (hf'.lipschitzOnWith) (fun x hx => hR' (mem_image_of_mem f' hx))).extend_finite_dimension
  set W := U ∩ ball 0 R
  have hW : IsOpen W := hU.inter isOpen_ball
  have hKW  := subset_inter hθU hR
  have hFW : ∀ x ∈ W, F x = ψ (f x) := fun x hx => by
    rw [← hFeq hx.2]; simp [hff' hx.1]
  have hIBP := integral_mul_fderiv_of_lipschitz hF hθ1 hθs e
  have hdθ0 : ∀ x ∉ tsupport θ, fderiv ℝ θ x e = 0 := fun x hx => by
    rw [show fderiv ℝ θ x = 0 from Function.notMem_support.mp
      (fun h => hx (support_fderiv_subset ℝ h))]
    rfl
  have hθ0 : ∀ x ∉ tsupport θ, θ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have L : ∫ x in U, ψ (f x) * fderiv ℝ θ x e = ∫ x, F x * fderiv ℝ θ x e := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ tsupport θ
      · simp [hFW x (hKW hx)]
      · simp [*]
    · intro x hx
      simp [hdθ0 x (fun h => hx (hθU h))]
  have Rr : ∫ x in U, fderiv ℝ ψ (f x) (fderiv ℝ f x e) * θ x = ∫ x, fderiv ℝ F x e * θ x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (f := fun x => fderiv ℝ F x e * θ x)
      (fun x hx => by simp [hθ0 x (fun h => hx (hθU h))])]
    refine setIntegral_congr_ae hU.measurableSet ?_
    have hd := ae_differentiableAt_of_lipschitzOnWith hU hf
    rw [ae_restrict_iff' hU.measurableSet] at hd
    filter_upwards [hd] with x hdx hxU
    by_cases hx : x ∈ tsupport θ
    · have hev : F =ᶠ[𝓝 x] ψ ∘ f :=
        Filter.eventually_of_mem (hW.mem_nhds (hKW hx)) hFW
      rw [hev.fderiv_eq, fderiv_comp x ((hψ.differentiable one_ne_zero) _) (hdx hxU)]
      rfl
    · simp [*]
  simp [*]

/-! ### Composition with a bi-Lipschitz map in `L²` -/

section BiLip

variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : ℝ≥0}

lemma eLpNorm_comp_bilip_le {V : Set ℂ} (hm : MapsTo f Ω V) (hg : LipschitzOnWith K f.symm V) (H : ℂ → ℂ) :
    eLpNorm (H ∘ f) 2 (volume.restrict Ω) ≤ K * eLpNorm H 2 (volume.restrict V) := by
  have emb : MeasurableEmbedding (f : ℂ → ℂ) := f.toMeasurableEquiv.measurableEmbedding
  rw [← emb.eLpNorm_map_measure]
  have h := eLpNorm_le_of_measure_le_smul (map_restrict_le_bilip hm hg) (f := H) (p := 2)
  simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    Nat.cast_ofNat, mul_inv_cancel₀ (two_ne_zero : (2:ℝ) ≠ 0), ENNReal.rpow_one, smul_eq_mul] using h

/-- If `W_k → W` in `L²(ℂ)`, then `∫_Ω (W_k ∘ f) c → ∫_Ω (W ∘ f) c` for `c ∈ L²(Ω)`. -/
lemma tendsto_setIntegral_comp_mul
    (hg : LipschitzOnWith K f.symm (f '' Ω)) {W : ℕ → ℂ → ℂ} {W₀ : ℂ → ℂ}
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
      (K * eLpNorm (W k - W₀) 2 volume).toReal * (eLpNorm c 2 (volume.restrict Ω)).toReal := by
    intro k
    rw [← integral_sub (hint (hW k)) (hint hW₀)]
    have e : (fun x => W k (f x) * c x - W₀ (f x) * c x) = fun x => (W k - W₀) (f x) * c x := by
      simp [sub_mul]
    rw [e]
    refine (norm_integral_mul_le_eLpNorm (hm ((hW k).sub hW₀)) hc).trans ?_
    gcongr
    · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ((hW k).sub hW₀).eLpNorm_ne_top
    · exact (eLpNorm_comp_bilip_le (mapsTo_image ..) hg _).trans
        (mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _)
  refine squeeze_zero ((by norm_num)) hbound ?_
  have : Tendsto (fun k => (K * eLpNorm (W k - W₀) 2 volume).toReal) atTop (𝓝 0) := by
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

section

variable (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω) (hg : LipschitzOnWith K f.symm (f '' Ω))
include hf hg hΩ

/-- The chain rule in weak form: for `v ∈ H¹(f(Ω))` with weak gradient `G` and a test function
`θ` on `Ω`, `∫_Ω (v ∘ f) ∂_i θ = -∫_Ω (∑_j (∂_i f)_j (G_j ∘ f)) θ`. -/
theorem integral_comp_mul_fderiv_bilip {v : L2 (f '' Ω)} {G : Fin 2 → L2 (f '' Ω)}
    (hG : IsWeakGradient (f '' Ω) v G) {θ : ℂ → ℂ} (hθ : TestFunction Ω θ) (i : Fin 2) :
    ∫ x in Ω, (v : ℂ → ℂ) (f x) * fderiv ℝ θ x (coordDir i) =
      -∫ x in Ω, chainGrad f (fun j => (G j : ℂ → ℂ)) i x * θ x := by
  have hΩ'  := f.isOpenMap Ω hΩ
  set V := extZero (f '' Ω) v
  set Gx : Fin 2 → ℂ → ℂ := fun j => extZero (f '' Ω) (G j)
  have hV  := memLp_extZero hΩ'.measurableSet v
  have hGx  := fun j => memLp_extZero hΩ'.measurableSet (G j)
  set r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hr : ∀ k, 0 < r k := fun k => by positivity
  set φ : ℕ → ContDiffBump (0 : ℂ) := fun k => ⟨r k / 2, r k, by simp [*], by simp [*]⟩
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
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
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
  have hk_eq  := fun k =>
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
    simp only [Gx, c, chainGrad, extZero, indicator_of_mem (mem_image_of_mem f hx), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [← e1, hlim, e2]

lemma memLp_chainGrad (G : Fin 2 → L2 (f '' Ω)) (i : Fin 2) :
    MemLp (chainGrad f (fun j => (G j : ℂ → ℂ)) i) 2 (volume.restrict Ω) := by
  have : chainGrad f (fun j => (G j)) i =
      ∑ j, fun x => (coordRe j (fderiv ℝ f x (coordDir i))) * (G j) (f x) := rfl
  rw [this]
  refine memLp_finset_sum' _ fun j _ => ?_
  refine (memLp_comp_bilip hg (Lp.memLp (G j))).of_le_mul (c := K) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_coordRe_fderiv f i j)).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (G j)).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_restrict hg))
  · rw [ae_restrict_iff' hΩ.measurableSet]
    refine Eventually.of_forall fun x hx => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Function.comp_apply]
    gcongr
    refine (abs_coordRe_le j _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    rw [norm_coordDir, mul_one]
    exact norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hx) hf

/-- **The Sobolev chain rule for bi-Lipschitz maps.** If `v ∈ H¹(f(Ω))` has weak gradient `G`
and `u = v ∘ f` a.e. on `Ω`, then `u` has weak gradient `∂_i u = ∑_j (∂_i f)_j (G_j ∘ f)`. -/
theorem isWeakGradient_comp_bilip {v : L2 (f '' Ω)} {G : Fin 2 → L2 (f '' Ω)}
    (hG : IsWeakGradient (f '' Ω) v G) {u : L2 Ω}
    (hu : (u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun x => (v : ℂ → ℂ) (f x)) :
    IsWeakGradient Ω u (fun i => (memLp_chainGrad hΩ hf hg G i).toLp _) := by
  intro θ hθ i
  have e : ∫ x in Ω, (u : ℂ → ℂ) x * fderiv ℝ θ x (coordDir i) =
      ∫ x in Ω, (v : ℂ → ℂ) (f x) * fderiv ℝ θ x (coordDir i) :=
    integral_congr_ae (hu.mono fun x hx => by simp [hx])
  rw [e, integral_comp_mul_fderiv_bilip hΩ hf hg hG hθ i]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(memLp_chainGrad hΩ hf hg G i).coeFn_toLp] with x hx
  rw [hx]

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
