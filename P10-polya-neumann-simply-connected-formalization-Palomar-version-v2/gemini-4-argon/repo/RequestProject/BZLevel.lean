module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import RequestProject.BZMollify

/-!
# Level sets of transversal smooth functions are smooth graphs (towards External theorem BZ)

* `exists_level_graph`: if `G(x, y)` is smooth and increases at a definite rate in `y`, its level
  set `G = ε` is locally the graph of a smooth function (implicit function theorem plus
  monotonicity);
* `exists_smooth_extension`: a function smooth near `[-r, r]` agrees there with a globally smooth,
  globally Lipschitz function;
* `smoothChart_of_level`: near a point `p` of the level set `ρ = ε` of a smooth function `ρ` that
  is transversal to a Lipschitz vector field, the superlevel set `{ρ > ε}` has a smooth graph
  chart in the sense of `IsSmoothDomain`.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal ContDiff ComplexConjugate

noncomputable section

namespace PolyaNeumann

/-- Smooth global extension by a cutoff. -/
lemma exists_smooth_extension  {r r₂ : ℝ} (hr : 0 < r) (hrr : r < r₂)
    (hf : ∀ x, |x| < r₂ → ContDiffAt ℝ ∞ f₀ x) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ (∃ K, LipschitzWith K F) ∧ ∀ x, |x| ≤ r → F x = f₀ x := by
  set χ : ContDiffBump (0 : ℝ) := ⟨r, (r + r₂) / 2, hr, by linarith⟩
  set F : ℝ → ℝ := fun x => χ x * f₀ x
  have hzero : ∀ x, (r + r₂) / 2 ≤ |x| → χ x = 0 := fun x hx => by
    rw [← Function.notMem_support, χ.support_eq, mem_ball, Real.dist_eq, sub_zero]
    exact not_lt.mpr hx
  have hF : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : |x| < r₂
    · exact χ.contDiff.contDiffAt.mul (hf x hx)
    · have hev : F =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [((continuous_abs.tendsto x).eventually (lt_mem_nhds (by push_neg at hx; linarith)) : ∀ᶠ y in 𝓝 x, (r + r₂) / 2 < |y|)] with y hy
        simp [F, hzero y hy.le]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  refine ⟨F, hF, ContDiff.lipschitzWith_of_hasCompactSupport (by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((r + r₂) / 2)) fun x hx => ?_
    rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
    simp [F, hzero x hx.le]) hF (by simp), fun x hx => ?_⟩
  simp [F, χ.one_of_mem_closedBall (by rwa [mem_closedBall, Real.dist_eq, sub_zero])]

/-- A positive lower bound for difference quotients bounds the derivative. -/
lemma le_deriv_of_slope  {g' y₀ κ δ : ℝ} (hg : HasDerivAt g g' y₀) (hδ : 0 < δ)
    (h : ∀ y, y₀ < y → y < y₀ + δ → g y₀ + κ * (y - y₀) ≤ g y) : κ ≤ g' := by
  refine ge_of_tendsto (hg.tendsto_slope.mono_left (nhdsWithin_mono _ (show Ioi y₀ ⊆ {y₀}ᶜ from fun y hy => ne_of_gt hy))) ?_
  filter_upwards [Ioo_mem_nhdsGT (show y₀ < y₀ + δ by linarith)] with y hy
  rw [slope_def_field, le_div_iff₀ (by linarith [hy.1])]
  linarith [h y hy.1 hy.2]

/-- **Level sets of monotone smooth functions are smooth graphs.** -/
theorem exists_level_graph {G : ℝ → ℝ → ℝ} (hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ => G q.1 q.2))
    {r₂ h h' κ ε : ℝ} (hκ : 0 < κ) (hh' : 0 < h') (hh : h' < h)
    (hmono : ∀ x, |x| < r₂ → ∀ y₁ y₂, -h < y₁ → y₁ ≤ y₂ → y₂ < h →
      G x y₁ + κ * (y₂ - y₁) ≤ G x y₂)
    (hlo : ∀ x, |x| < r₂ → G x (-h') < ε) (hhi : ∀ x, |x| < r₂ → ε < G x h') :
    ∃ f₀ : ℝ → ℝ, (∀ x, |x| < r₂ → |f₀ x| < h' ∧ G x (f₀ x) = ε) ∧
      (∀ x, |x| < r₂ → ∀ y, |y| < h → (ε < G x y ↔ f₀ x < y)) ∧
      (∀ x, |x| < r₂ → ContDiffAt ℝ ∞ f₀ x) := by
  have hGc : ∀ x, Continuous (G x) := fun x =>
    hG.continuous.comp (continuous_const.prodMk continuous_id)
  have hex : ∀ x, |x| < r₂ → ∃ y, |y| < h' ∧ G x y = ε := by
    intro x hx
    obtain ⟨y, hy, hyε⟩ := intermediate_value_Ioo (by linarith) (hGc x).continuousOn
      (⟨hlo x hx, hhi x hx⟩)
    exact ⟨y, abs_lt.mpr ⟨hy.1, hy.2⟩, hyε⟩
  -- uniqueness of the crossing
  classical
  set f₀ : ℝ → ℝ := fun x => if hx : |x| < r₂ then (hex x hx).choose else 0
  have hf₀ : ∀ x, |x| < r₂ → |f₀ x| < h' ∧ G x (f₀ x) = ε := fun x hx => by
    simp [f₀, dif_pos hx]; exact (hex x hx).choose_spec
  refine ⟨f₀, hf₀, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨h1, h2⟩ := hf₀ x hx
    constructor
    · intro hεy
      by_contra hle
      push_neg at hle
      have := hmono x hx y (f₀ x) (abs_lt.mp hy).1 hle (by linarith [(abs_lt.mp h1).2])
      nlinarith
    · intro hlt
      have := hmono x hx (f₀ x) y (by linarith [(abs_lt.mp h1).1]) hlt.le (abs_lt.mp hy).2
      nlinarith
  · intro x₀ hx₀
    obtain ⟨hb₀, hG₀⟩ := hf₀ x₀ hx₀
    set Gt : ℝ × ℝ → ℝ := fun q => G q.1 q.2
    set a := (x₀, f₀ x₀)
    set G' := fderiv ℝ Gt a
    -- the partial derivative in `y` is at least `κ`
    have hpart : κ ≤ G' (0, 1) := by
      refine le_deriv_of_slope (by
        have h1 : HasDerivAt (fun y => (x₀, y)) (0, 1) (f₀ x₀) :=
          (hasDerivAt_const _ x₀).prodMk (hasDerivAt_id _)
        simpa [Gt, a, Function.comp_def] using (((hG.differentiable (by simp)).differentiableAt).hasFDerivAt.comp_hasDerivAt (f₀ x₀) h1)) (δ := h - h') (by linarith) fun y hy1 hy2 => ?_
      exact hmono x₀ hx₀ (f₀ x₀) y (by linarith [(abs_lt.mp hb₀).1]) hy1.le (by linarith [(abs_lt.mp hb₀).2])
    have cdf : ContDiffAt ℝ ∞ Gt a := hG.contDiffAt
    have pn : ∞ ≠ 0 := by simp
    have if₂ : (fderiv ℝ Gt a ∘L .inr ℝ ℝ ℝ).IsInvertible :=
      ⟨(LinearEquiv.ofBijective (G'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).toLinearMap
        (show Function.Bijective (G'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) by
          have hne : G' (0, 1) ≠ 0 := by linarith
          have hlin : ∀ y : ℝ, (G'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) y = y * G' (0, 1) := by
            intro y
            simp
            rw [show ((0 : ℝ), y) = y • (0, 1) by simp, map_smul, smul_eq_mul]
          refine ⟨fun y₁ y₂ hy => ?_, fun z => ⟨z / G' (0, 1), ?_⟩⟩
          · rw [hlin, hlin] at hy
            exact mul_right_cancel₀ hne hy
          · rw [hlin, div_mul_cancel₀ _ hne])).toContinuousLinearEquiv, by ext x; rfl⟩
    set φ := cdf.implicitFunction pn if₂
    have hφc : ContDiffAt ℝ ∞ φ x₀ := cdf.contDiffAt_implicitFunction pn if₂
    have hφ₀ : φ x₀ = f₀ x₀ := cdf.implicitFunction_apply_self pn if₂
    have hφnear : ∀ᶠ x in 𝓝 x₀, |φ x| < h := by
      exact (continuous_abs.continuousAt.comp hφc.continuousAt).eventually (gt_mem_nhds (by show |φ x₀| < h; rw [hφ₀]; linarith))
    exact hφc.congr_of_eventuallyEq (by
      filter_upwards [cdf.eventually_apply_implicitFunction pn if₂, hφnear, (continuous_abs.tendsto x₀).eventually (gt_mem_nhds hx₀)] with x h1 h2 h3
      obtain ⟨h4, h5⟩ := hf₀ x h3
      refine (show ∀ x, |x| < r₂ → ∀ y₁ y₂, |y₁| < h → |y₂| < h → G x y₁ = ε → G x y₂ = ε → y₁ = y₂ by
        intro x hx y₁ y₂ h1 h2 e1 e2
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := hmono x hx y₁ y₂ (abs_lt.mp h1).1 hlt.le (abs_lt.mp h2).2
          nlinarith
        · have := hmono x hx y₂ y₁ (abs_lt.mp h2).1 hlt.le (abs_lt.mp h1).2
          nlinarith) x h3 _ _ (by linarith) h2 h5 ?_
      simpa [Gt, a, hG₀] using h1)

/-- Coordinates of the rotated chart: `P(x, y) = p + conj(c) (x + i y)`. -/
def chartMap (p c : ℂ) (x y : ℝ) : ℂ := p + conj c * ((x : ℂ) + (y : ℂ) * Complex.I)

lemma norm_chartMap_sub  (hc : ‖c‖ = 1) x y :
    ‖chartMap p c x y - p‖ ≤ |x| + |y| := by
  simp [chartMap, hc]
  refine (norm_add_le _ _).trans ?_
  simp

theorem smoothChart_of_level  (hρ : ContDiff ℝ ∞ ρ) (hρL : LipschitzWith 2 ρ)
     {LX} (hX : LipschitzWith LX X)   (hτ : 0 < τ)
    (hκ : 0 < κ) (hQ : IsTransversalOn ρ X U τ κ) {D : Set ℂ} {ε R : ℝ}  (hR : 0 < R)
    (hpU : ball p R ⊆ U) (hp : ρ p = ε) (hD : ∀ w ∈ ball p R, w ∈ D ↔ ε < ρ w) :
    ∃ (c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ),
      ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧ ContDiff ℝ ∞ f ∧ LipschitzWith K f ∧ f 0 = 0 ∧
      (∀ x : ℝ, |x| < r → |f x| < h) ∧
      ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
        (w ∈ D ↔ f (c * (w - p)).re < (c * (w - p)).im) := by
  -- the field does not vanish at `p`
  set m : ℝ := ‖X p‖
  have hm : 0 < m := by
    have h1 := hQ p (hpU (mem_ball_self hR)) τ hτ.le le_rfl
    rcases (norm_nonneg (X p)).eq_or_lt with h0 | h0
    · rw [eq_comm, norm_eq_zero] at h0
      rw [h0, mul_zero, add_zero] at h1
      nlinarith
    · exact h0
  -- uniform transversality along the fixed direction `X p`
  set rb : ℝ := min R (κ / (4 * LX + 1))
  -- the unit direction and the rotation
  have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  set e : ℂ := X p * (m : ℂ)⁻¹
  have he : X p = (m : ℂ) * e := by
    simp [e]; rw [mul_left_comm, mul_inv_cancel₀ hmC, mul_one]
  have hdir : ∀ z ∈ ball p rb, ∀ s, 0 ≤ s → s ≤ τ * m →
      ρ z + κ / (2 * m) * s ≤ ρ (z + s * e) := by
    intro z hz s hs0 hsτ
    have := (show ∀ z ∈ ball p rb, ∀ t, 0 ≤ t → t ≤ τ → ρ z + κ / 2 * t ≤ ρ (z + t * X p) by
      intro z hz t ht0 htτ
      have h1 := hQ z (hpU (ball_subset_ball (min_le_left _ _) hz)) t ht0 htτ
      have h2 : |ρ (z + t * X p) - ρ (z + t * X z)| ≤ 2 * (t * (LX * rb)) := by
        have := hρL.dist_le_mul (z + t * X p) (z + t * X z)
        rw [Real.dist_eq, dist_eq_norm, show z + t * X p - (z + t * X z) = t * (X p - X z) by ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at this
        refine this.trans ?_
        push_cast
        have h3 : ‖X p - X z‖ ≤ LX * rb := by
          rw [← dist_eq_norm]
          refine (hX.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ LX.2)
          rw [dist_comm]; exact (mem_ball.mp hz).le
        have := mul_le_mul_of_nonneg_left h3 ht0
        linarith
      have h4 : LX * rb ≤ κ / 4 := by
        have h5 : rb ≤ κ / (4 * LX + 1) := min_le_right _ _
        have h6 : LX * (κ / (4 * LX + 1)) ≤ κ / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
        nlinarith
      have := (abs_le.mp h2).1
      nlinarith) z hz (s / m) (div_nonneg hs0 hm.le) (by rw [div_le_iff₀ hm]; linarith)
    rw [he, show (s / m : ℝ) * ((m : ℂ) * e) = (s : ℂ) * e by
      rw [← mul_assoc]; congr 1; push_cast; field_simp] at this
    have : κ / 2 * (s / m) = κ / (2 * m) * s := by field_simp
    linarith
  set c : ℂ := Complex.I * conj e
  have hc : ‖c‖ = 1 := by
    simp [c, e, abs_of_pos hm]
    exact mul_inv_cancel₀ hm.ne'
  -- the graph function
  set G : ℝ → ℝ → ℝ := fun x y => ρ (chartMap p c x y)
  set h : ℝ := min (rb / 4) (τ * m / 4)
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  set κ'' : ℝ := κ / (2 * m)
  set r₂ : ℝ := min (κ'' * h / 4) (h / 2)
  have hr₂ : 0 < r₂ := lt_min (by positivity) (by positivity)
  have hr₂h : r₂ ≤ h / 2 := min_le_right _ _
  have hr₂κ : r₂ ≤ κ'' * h / 4 := min_le_left _ _
  have hhrb : h ≤ rb / 4 := min_le_left _ _
  have hhτ : h ≤ τ * m / 4 := min_le_right _ _
  have hmono : ∀ x, |x| < r₂ → ∀ y₁ y₂, -h < y₁ → y₁ ≤ y₂ → y₂ < h →
      G x y₁ + κ'' * (y₂ - y₁) ≤ G x y₂ := by
    intro x hx y₁ y₂ h1 h12 h2
    simp [G]
    rw [(show ∀ x y₁ y₂ : ℝ, chartMap p c x y₂ = chartMap p c x y₁ + (y₂ - y₁ : ℝ) * e by
      intro x y₁ y₂
      simp [chartMap, c]
      ring_nf
      rw [Complex.I_sq]; ring) x y₁ y₂]
    refine hdir _ ?_ _ (by linarith) (by linarith)
    rw [mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (norm_chartMap_sub hc x y₁) ?_
    have:= abs_lt.mpr ⟨h1, by linarith⟩
    linarith
  have hG0 : ∀ x, |G x 0 - ε| ≤ 2 * |x| := by
    intro x
    have := hρL.dist_le_mul (chartMap p c x 0) p
    rw [Real.dist_eq, dist_eq_norm, hp] at this
    refine this.trans ?_
    have := norm_chartMap_sub (p := p) hc x 0
    simp at this
    push_cast; linarith
  have hhi : ∀ x, |x| < r₂ → ε < G x (h / 2) := by
    intro x hx
    have h1 := hmono x hx 0 (h / 2) (by linarith) (by linarith) (by linarith)
    have h2 := (abs_le.mp (hG0 x)).1
    nlinarith
  obtain ⟨f₀, hf₀, hf₀iff, hf₀c⟩ :=
    exists_level_graph (by
      have h1 : ContDiff ℝ ∞ fun q : ℝ × ℝ => (q.1 : ℂ) :=
        Complex.ofRealCLM.contDiff.comp contDiff_fst
      have h2 : ContDiff ℝ ∞ fun q : ℝ × ℝ => (q.2 : ℂ) :=
        Complex.ofRealCLM.contDiff.comp contDiff_snd
      exact hρ.comp (contDiff_const.add (contDiff_const.mul (h1.add (h2.mul contDiff_const))))) (by positivity) (by linarith : 0 < h / 2) (by linarith) hmono (by
      intro x hx
      have h1 := hmono x hx (-(h / 2)) 0 (by linarith) (by linarith) hh
      have h2 := (abs_le.mp (hG0 x)).2
      nlinarith) hhi
  obtain ⟨F, hFc, ⟨K, hFl⟩, hFf⟩ :=
    exists_smooth_extension (r := r₂ / 2) (by positivity) (by linarith) hf₀c
  have hf00 : f₀ 0 = 0 := by
    have h0 : |0| < r₂ := by simpa using hr₂
    obtain ⟨hb, hε⟩ := hf₀ 0 h0
    have hG00 : G 0 0 = ε := by simp [G, chartMap, hp]
    rcases lt_trichotomy (f₀ 0) 0 with hlt | heq | hgt
    · have := (hf₀iff 0 h0 0 (by simpa using hh)).mpr hlt
      linarith
    · exact heq
    · have := hmono 0 h0 0 (f₀ 0) (by linarith) hgt.le (by linarith [(abs_lt.mp hb).2])
      nlinarith
  refine ⟨c, r₂ / 2, h, K, F, hc, by positivity, hh, hFc, hFl, ?_, ?_, ?_⟩
  · rw [hFf 0 (by simp; positivity), hf00]
  · intro x hx
    rw [hFf x hx.le]
    have := (hf₀ x (by linarith)).1
    linarith
  · intro w hwx hwy
    set x := (c * (w - p)).re
    set y := (c * (w - p)).im
    have h_inl : chartMap p c (c * (w - p)).re (c * (w - p)).im = w := by
      simp only [chartMap]
      rw [Complex.re_add_im, ← mul_assoc, show conj c * c = 1 by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; norm_num, one_mul]
      ring
    have hw : chartMap p c x y = w := h_inl
    rw [hD w (by
      rw [mem_ball, dist_eq_norm, ← hw]
      refine lt_of_le_of_lt (norm_chartMap_sub hc x y) ?_
      have : rb ≤ R := min_le_left _ _
      linarith), hFf x hwx.le, ← hf₀iff x (by linarith) y hwy, ← hw]

end PolyaNeumann

end
