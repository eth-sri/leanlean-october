module

public import GradedNear.Defs

/-!
# Decay of the Laplace transform

For `f` satisfying Condition 1, `F(x + iY) → 0` as `|Y| → ∞`, uniformly for `x` in a compact
interval.

The proof is by integration by parts on `[0, x₀]` (`f` vanishes on `[x₀, ∞)`):
`z F(z) = f(0) + ∫₀^{x₀} f'(t) e^{-zt} dt`. The derivative `f'` is bounded on `(0, x₀]`, because
`|f''| ≤ B` makes it Lipschitz on `(0, x₀)`. Hence `|F(x + iY)| ≤ C / |Y|` with
`C = |f(0)| + K x₀ e^{X x₀}`, uniformly for `x ∈ [-X, X]`, where `K` bounds `|f'|`.
-/

@[expose] public section

namespace GradedNear

namespace Decay

open MeasureTheory Set

/-- The derivative of a `Condition1` function is bounded on `(0, x₀]`. -/
lemma exists_abs_deriv_le {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Ioc 0 x₀, |deriv f t| ≤ K := by
  have hx₀ := hf.pos
  have hmid : x₀ / 2 ∈ Ioo (0 : ℝ) x₀ := ⟨by linarith, by linarith⟩
  have hd := hf.smooth.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)
  refine ⟨max (|deriv f (x₀ / 2)| + B * x₀) |deriv f x₀|, (abs_nonneg _).trans (le_max_right ..),
    fun t ht => ?_⟩
  rcases ht.2.eq_or_lt with h | h
  · grind
  have hmv := (convex_Ioo (0 : ℝ) x₀).norm_image_sub_le_of_norm_deriv_le (fun t ht =>
    (hd.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
    hf.bound hmid ⟨ht.1, h⟩
  simp at hmv
  have := mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [ht.1], by linarith⟩ : |t - x₀ / 2| ≤ x₀)
    ((abs_nonneg _).trans (hf.bound _ hmid))
  grind

/-- Since `f` vanishes on `[x₀, ∞)`, the Laplace transform is an integral over `[0, x₀]`. -/
lemma laplace_eq_intervalIntegral {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (z : ℂ) :
    laplace f z = ∫ t in (0 : ℝ)..x₀, (f t : ℂ) * Complex.exp (-(z * t)) := by
  rw [intervalIntegral.integral_of_le hf.pos.le, laplace]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self fun t ht => by simp [hf.vanish t (not_lt.1 fun h => ht.2 ⟨ht.1, h.le⟩)]

/-- Integration by parts: `z F(z) = f(0) + ∫₀^{x₀} f'(t) e^{-zt} dt`. -/
lemma mul_laplace_eq {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) {K : ℝ}
    (hK : ∀ t ∈ Ioc 0 x₀, |deriv f t| ≤ K) (z : ℂ) :
    z * laplace f z =
      (f 0 : ℂ) + ∫ t in (0 : ℝ)..x₀, ((deriv f t : ℝ) : ℂ) * Complex.exp (-(z * t)) := by
  have hx₀ := hf.pos
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => (f t : ℂ)) (v := fun t : ℝ => Complex.exp (-(z * t)))
    (u' := fun t => ((deriv f t : ℝ) : ℂ)) (v' := fun t => Complex.exp (-(z * t)) * -(z * 1))
    (by rw [uIcc_of_le hx₀.le]
        exact Complex.continuous_ofReal.comp_continuousOn (hf.cont.mono Icc_subset_Ici_self))
    (by fun_prop) (fun t ht => by
      rw [min_eq_left hx₀.le, max_eq_right hx₀.le] at ht
      exact ((hf.smooth.differentiableOn (by norm_num) t ht).differentiableAt
        (isOpen_Ioo.mem_nhds ht)).hasDerivAt.ofReal_comp)
    (fun t _ => (((hasDerivAt_id' (t : ℂ)).const_mul z).neg.cexp).comp_ofReal)
    ((intervalIntegrable_const (c := K)).mono_fun'
      (Complex.measurable_ofReal.comp (measurable_deriv f)).aestronglyMeasurable (by
        rw [uIoc_of_le hx₀.le]
        exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by simp_all))
    (Continuous.intervalIntegrable (by fun_prop) ..)
  rw [show (∫ t in (0 : ℝ)..x₀, (f t : ℂ) * (Complex.exp (-(z * t)) * -(z * 1))) = -z * laplace f z by
    rw [laplace_eq_intervalIntegral hf, ← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring, hf.vanish x₀ le_rfl] at hibp
  simp at hibp
  grind

end Decay

theorem laplace_decay {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (X : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Set.Icc (-X) X, ∀ Y : ℝ, M ≤ |Y| →
      ‖laplace f ((x : ℂ) + (Y : ℂ) * Complex.I)‖ ≤ ε := by
  obtain ⟨K, hK0, hK⟩ := Decay.exists_abs_deriv_le hf
  have hx₀ := hf.pos
  refine ⟨(|f 0| + K * Real.exp (X * x₀) * x₀) / ε + 1, by positivity, fun x hx Y hY => ?_⟩
  set z : ℂ := (x : ℂ) + (Y : ℂ) * Complex.I
  have hz : |Y| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x₀)
    (C := K * Real.exp (X * x₀))
    (f := fun t : ℝ => ((deriv f t : ℝ) : ℂ) * Complex.exp (-(z * t))) fun t ht => by
      rw [Set.uIoc_of_le hx₀.le] at ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      refine mul_le_mul (hK t ht) (Real.exp_le_exp.2 ?_) (by positivity) hK0
      simp [z]
      nlinarith [ht.1, ht.2, hx.1, hx.2]
  have h2 := (norm_add_le (f 0 : ℂ) _).trans (add_le_add le_rfl h)
  rw [← Decay.mul_laplace_eq hf hK, norm_mul, Complex.norm_real, sub_zero, abs_of_pos hx₀] at h2
  rw [div_add_one hε.ne', div_le_iff₀ hε] at hY
  by_contra hc
  nlinarith [Real.norm_eq_abs (f 0), mul_le_mul_of_nonneg_left (not_le.1 hc).le (abs_nonneg Y)]

end GradedNear
