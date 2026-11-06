import GradedNear.Tactics

import GradedNear.Defs

/-!
# Decay of the Laplace transform

For `f` satisfying Condition 1, `F(x + iY) → 0` as `|Y| → ∞`, uniformly for `x` in a compact
interval.

The proof is by integration by parts on `[0, x₀]` (`f` vanishes on `[x₀, ∞)`):
`z F(z) = f(0) + ∫₀^{x₀} f'(t) e^{-zt} dt`. The derivative `f'` is bounded on `(0, x₀]`, because
`|f''| ≤ B` makes it Lipschitz on `(0, x₀)`. Hence `|F(x + iY)| ≤ C / |Y|` with
`C = |f(0)| + K x₀ e^{X x₀}`, uniformly for `x ∈ [-X, X]`, where `K` bounds `|f'|`.
-/

namespace GradedNear

open MeasureTheory Set

section
variable {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B)
include hf

namespace Decay

/-- Since `f` vanishes on `[x₀, ∞)`, the Laplace transform is an integral over `[0, x₀]`. -/
lemma laplace_eq_intervalIntegral (z : ℂ) :
    laplace f z = ∫ t in (0 : ℝ)..x₀, ↑(f t) * Complex.exp (-(z * t)) := by
  rw [intervalIntegral.integral_of_le hf.pos.le]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self fun t ht => ?_

  simp [hf.vanish t (by grind)]

end Decay

theorem laplace_decay (X : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Set.Icc (-X) X, ∀ Y : ℝ, M ≤ |Y| →
      ‖laplace f (↑x + ↑Y * Complex.I)‖ ≤ ε := by

  have hd1 : ContDiffOn ℝ 1 (deriv f) (Ioo 0 x₀) :=
    hf.smooth.deriv_of_isOpen isOpen_Ioo (by norm_num)

  have hlip := (convex_Ioo (0 : ℝ) x₀).lipschitzOnWith_of_nnnorm_deriv_le
    (C := Real.toNNReal B) (fun t ht =>
      (hd1.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
    ) fun t ht => by
      exact_mod_cast (hf.bound t ht).trans (Real.le_coe_toNNReal B)
  letI : BoundedSpace (Ioo (0 : ℝ) x₀) := (Metric.isBounded_Ioo 0 x₀).boundedSpace_val
  have hb := hlip.to_restrict.isBounded_image (Bornology.IsBounded.all Set.univ)
  simp only [Set.image_univ, Set.range_domRestrict] at hb
  obtain ⟨K, hK0, hK⟩ := (hb.insert (deriv f x₀)).exists_pos_norm_le
  have hK (t : ℝ) (ht : t ∈ Ioc 0 x₀) : |deriv f t| ≤ K := by
    apply hK _
    grind
  have hx₀ := hf.pos
  set C := |f 0| + K * Real.exp (X * x₀) * x₀
  have hC0 : 0 ≤ C := by positivity
  refine ⟨(C + 1) / ε, by positivity, fun x hx Y hY => ?_⟩
  set z : ℂ := ↑x + ↑Y * Complex.I
  have hzre : z.re = x := by aesop
  have hzim : z.im = Y := by aesop
  have hX : 0 ≤ X := by grind
  have hbound : ‖z * laplace f z‖ ≤ C := by
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun t => ↑(f t)) (u' := fun t => ((deriv f t : ℝ) : ℂ))
      (v := fun t : ℝ => Complex.exp (-(z * t)))
      (v' := fun t : ℝ => -z * Complex.exp (-(z * t)))
      (by
        rw [uIcc_of_le hf.pos.le]
        exact Complex.continuous_ofReal.comp_continuousOn (hf.cont.mono Icc_subset_Ici_self))
      (by fun_prop)
      (by
        intro t ht
        rw [min_eq_left hf.pos.le, max_eq_right hf.pos.le] at ht
        exact ((hf.smooth.differentiableOn (by norm_num) t ht).differentiableAt
          (isOpen_Ioo.mem_nhds ht)).hasDerivAt.ofReal_comp)
      (by
        intro t _
        convert (((hasDerivAt_id t).ofReal_comp).const_mul (-z)).cexp using 1 <;>
          simp [neg_mul, mul_comm])
      (by
        refine (intervalIntegrable_const (c := K)).mono_fun' ?_ ?_
        · fun_prop
        · rw [uIoc_of_le hf.pos.le]
          refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
          simp_all)
      (by apply Continuous.intervalIntegrable; fun_prop)
    simp_rw [mul_left_comm _ (-z)] at hibp
    rw [intervalIntegral.integral_const_mul, ← Decay.laplace_eq_intervalIntegral hf,
      hf.vanish x₀ le_rfl] at hibp
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero, mul_one,
      zero_sub] at hibp
    rw [neg_mul, neg_eq_iff_eq_neg, neg_sub, sub_neg_eq_add] at hibp
    rw [hibp, add_comm]
    refine (norm_add_le _ _).trans (add_le_add (by simp) ?_)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x₀)
      (C := K * Real.exp (X * x₀))
      (f := fun t : ℝ => ((deriv f t : ℝ) : ℂ) * Complex.exp (-(z * t))) ?_
    · grind
    intro t ht
    rw [uIoc_of_le hx₀.le] at ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    refine mul_le_mul (hK t ht) ?_ (Real.exp_pos _).le hK0.le

    simp

    nlinarith [ht.1, ht.2, hx.1]
  rw [norm_mul] at hbound
  have hMz := hY.trans (hzim ▸ Complex.abs_im_le_norm z)
  rw [div_le_iff₀ hε] at hMz
  nlinarith

end

end GradedNear
