module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.VectorFTC
public import RequestProject.GreenWinding
public import RequestProject.PlanarNotation

/-!
# Winding numbers of closed Lipschitz curves

For a closed Lipschitz curve `γ` (`γ(2π) = γ(0)`) and `z ∉ γ([0, 2π])`:

* `PolyaNeumann.windingNumber_mem_range_intCast`: the winding number is an integer;
* `PolyaNeumann.continuousOn_windingNumber`: it is continuous off the curve;
* `PolyaNeumann.windingNumber_eq_zero_of_far`: it vanishes far from the curve;
* `PolyaNeumann.windingNumber_const_of_isPreconnected`: it is constant on preconnected sets
  avoiding the curve.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- The complex exponential is Lipschitz on closed balls about `0`. -/
lemma lipschitzOnWith_cexp_closedBall (R : ℝ) :
    LipschitzOnWith (Real.toNNReal (Real.exp R)) Complex.exp (closedBall 0 R) := by
  refine (convex_closedBall 0 R).lipschitzOnWith_of_nnnorm_deriv_le
    ((by fun_prop)) (fun x hx => ?_)
  rw [Complex.deriv_exp, ← NNReal.coe_le_coe, coe_nnnorm,
    Real.coe_toNNReal _ (by positivity), Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm x).trans (by simpa using hx))

/-- A continuous curve avoiding `z` on a compact interval stays at positive distance. -/
lemma exists_pos_le_norm_sub {γ : ℝ → ℂ} (hγ : Continuous γ) {a b : ℝ} {z : ℂ}
    (hz : ∀ θ ∈ Icc a b, γ θ ≠ z) : ∃ d > 0, ∀ θ ∈ Icc a b, d ≤ ‖γ θ - z‖ := by
  rcases (Icc a b).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, by simp [he]⟩
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    ((hγ.sub continuous_const).norm.continuousOn)
  refine ⟨‖γ θ₀ - z‖, norm_pos_iff.mpr (sub_ne_zero.mpr (hz θ₀ hθ₀)), fun θ hθ => ?_⟩
  exact hmin hθ

/-- The integrand `γ'/(γ - z)` is interval integrable where the curve avoids `z`. -/
lemma intervalIntegrable_deriv_div {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) {z : ℂ} (hz : ∀ θ ∈ Icc a b, γ θ ≠ z) :
    IntervalIntegrable (fun θ => deriv γ θ / (γ θ - z)) volume a b := by
  obtain ⟨d, hd, hdz⟩ := exists_pos_le_norm_sub hK.continuous hz
  refine IntervalIntegrable.mono_fun (intervalIntegrable_const (c := K / d)) ?_ ?_
  · exact ((measurable_deriv γ).div
      (hK.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    rw [norm_div, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) hd
      (hdz θ ⟨hθ.1.le, hθ.2⟩)

/-- Along an arc avoiding `z`, `exp(-∫ₐ^θ γ'/(γ - z)) (γ(θ) - z) = γ(a) - z`. -/
lemma exp_neg_integral_mul_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) {z : ℂ} (hz : ∀ θ ∈ Icc a b, γ θ ≠ z) :
    ∀ θ ∈ Icc a b,
      Complex.exp (-∫ t in a..θ, deriv γ t / (γ t - z)) * (γ θ - z) = γ a - z := by
  let P := fun x => ∫ t in a..x, deriv γ t / (γ t - z)
  have hi := intervalIntegrable_deriv_div hK hab hz
  have hP := absolutelyContinuousOnInterval_intervalIntegral_banach hi left_mem_uIcc
  obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn hP.continuousOn
  have he : AbsolutelyContinuousOnInterval (fun x => Complex.exp (-P x)) a b :=
    (lipschitzOnWith_cexp_closedBall R).comp_absolutelyContinuousOnInterval
      (fun x hx => by simpa using hR x hx) hP.neg
  have hg : AbsolutelyContinuousOnInterval (fun x => γ x - z) a b := (hK.sub (LipschitzWith.const z)).lipschitzOnWith.absolutelyContinuousOnInterval
  obtain ⟨C, hC⟩ := (he.smul hg).const_of_ae_hasDerivAt_zero (by
    filter_upwards [hi.ae_hasDerivAt_integral, hK.ae_differentiableAt_real] with x hx hdx h
    have hd := ((hx h a left_mem_uIcc).neg.cexp).mul (hdx.hasDerivAt.sub_const z)
    have hn := sub_ne_zero.mpr (hz x (uIcc_of_le hab ▸ h))
    convert hd using 1
    field_simp
    ring)
  intro x hx
  simpa [P] using (hC x (uIcc_of_le hab ▸ hx)).trans (hC a left_mem_uIcc).symm

/-- The winding number of a closed Lipschitz curve about a point off the curve is an
integer. -/
theorem windingNumber_mem_range_intCast {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ anglePeriod = γ 0) {z : ℂ} (hz : z ∉ γ '' angleInterval) :
    windingNumber γ z ∈ range ((↑) : ℤ → ℂ) := by
  have hθ : ∀ θ ∈ angleInterval, γ θ ≠ z := fun θ h h' => hz ⟨θ, h, h'⟩
  have h := exp_neg_integral_mul_eq hK Real.two_pi_pos.le hθ _ (right_mem_Icc.mpr Real.two_pi_pos.le)
  rw [hclosed, mul_eq_right₀ (sub_ne_zero.mpr (hθ 0 (left_mem_Icc.mpr Real.two_pi_pos.le)))] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨-n, ?_⟩
  rw [windingNumber, neg_eq_iff_eq_neg.mp hn]
  push_cast
  field_simp

/-- The winding number is continuous off the curve. -/
theorem continuousOn_windingNumber {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) :
    ContinuousOn (windingNumber γ) (γ '' angleInterval)ᶜ := by
  have hpi : 0 ≤ anglePeriod := by positivity
  
  intro z₀ hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ((isCompact_Icc.image hK.continuous).isClosed).isOpen_compl z₀ hz₀
  have hfar : ∀ z ∈ ball z₀ (ε / 2), ∀ θ ∈ angleInterval, ε / 2 ≤ ‖γ θ - z‖ := by
    intro z hz θ hθ
    have h1 : ε ≤ ‖γ θ - z₀‖ := by
      by_contra h
      push_neg at h
      exact hball (mem_ball_iff_norm.mpr h) (mem_image_of_mem γ hθ)
    have h2 : ‖z - z₀‖ < ε / 2 := mem_ball_iff_norm.mp hz
    calc _ = ε - ε / 2 := by ring
      _ ≤ ‖γ θ - z₀‖ - ‖z - z₀‖ := by linarith
      _ ≤ _ := by
          grind [norm_sub_norm_le (γ θ - z₀) (z - z₀)]
  refine ContinuousAt.continuousWithinAt ?_
  
  refine continuousAt_const.mul ?_
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => K / (ε / 2))
    ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun z => ((measurable_deriv γ).div
      (hK.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds z₀ (half_pos hε)] with z hz
    refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hpi] at hθ
    rw [norm_div]
    exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) (half_pos hε)
      ((by grind))
  · refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hpi] at hθ
    have hne : γ θ - z₀ ≠ 0 := by
      grind
    fun_prop

/-- `|wind(γ, z)| ≤ K / dist(z, γ)`: if every point of the curve is at distance at least
`d > K` from `z`, the winding number is `0` (for a closed curve). -/
theorem windingNumber_eq_zero_of_far {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ anglePeriod = γ 0) {z : ℂ} {d : ℝ} (hd : (K : ℝ) < d)
    (hzd : ∀ θ ∈ angleInterval, d ≤ ‖γ θ - z‖) : windingNumber γ z = 0 := by
  have hd0  := lt_of_le_of_lt K.coe_nonneg hd
  have hz : z ∉ γ '' angleInterval := by
    rintro ⟨θ, hθ, rfl⟩
    have := hzd θ hθ
    rw [sub_self, norm_zero] at this
    linarith
  obtain ⟨n, hn⟩ := windingNumber_mem_range_intCast hK hclosed hz
  have hbound : ‖windingNumber γ z‖ < 1 := by
    have hint : ‖∫ₚ θ, deriv γ θ / (γ θ - z)‖ ≤ K / d * |anglePeriod - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
      rw [uIoc_of_le (by positivity)] at hθ
      have h1 := hzd θ ⟨hθ.1.le, hθ.2⟩
      rw [norm_div]
      exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) hd0 h1
    rw [windingNumber, norm_mul, norm_inv]
    have h2pi : ‖(anglePeriod * Complex.I : ℂ)‖ = anglePeriod := by
      norm_num
    rw [h2pi, sub_zero, abs_of_pos (by positivity)] at *
    calc _
        ≤ anglePeriod⁻¹ * (K / d * anglePeriod) := by gcongr
      _ = K / d := by field_simp
      _ < 1 := (div_lt_one hd0).mpr hd
  rw [← hn] at hbound ⊢
  have : |(n : ℝ)| < 1 := by
    rwa [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at hbound
  have h1 : |n| < 1 := by
    rw [← Int.cast_abs] at this; exact_mod_cast this
  have  := abs_eq_zero.mp (le_antisymm (by omega) (abs_nonneg n))
  simp [this]

instance : DiscreteTopology (range ((↑) : ℤ → ℂ)) :=
  Complex.isometry_intCast.isEmbedding.toHomeomorph.symm.isEmbedding.discreteTopology

/-- The winding number of a closed Lipschitz curve is constant on every preconnected set
avoiding the curve. -/
theorem windingNumber_const_of_isPreconnected {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ anglePeriod = γ 0) {S : Set ℂ} (hS : IsPreconnected S)
    (hSγ : Disjoint S (γ '' angleInterval)) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    windingNumber γ z = windingNumber γ w := by
  have hsub : S ⊆ (γ '' angleInterval)ᶜ := (by grind)
  exact hS.constant_of_mapsTo (isDiscrete_iff_discreteTopology.mpr inferInstance)
    ((continuousOn_windingNumber hK).mono hsub)
    (fun x hx => windingNumber_mem_range_intCast hK hclosed (hsub hx)) hz hw

end PolyaNeumann

end
