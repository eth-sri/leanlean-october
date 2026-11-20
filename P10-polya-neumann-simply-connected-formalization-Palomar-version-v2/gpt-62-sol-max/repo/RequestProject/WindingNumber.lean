module

public import RequestProject.GreenWinding
public import RequestProject.IntervalFTC

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
  refine (convex_closedBall (0 : ℂ) R).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => Complex.differentiableAt_exp) (fun x hx => ?_)
  rw [Complex.deriv_exp, ← NNReal.coe_le_coe, coe_nnnorm,
    Real.coe_toNNReal _ (Real.exp_pos R).le, Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm x).trans (by simp_all))

/-- A continuous curve avoiding `z` on a compact interval stays at positive distance. -/
lemma exists_pos_le_norm_sub {γ : ℝ → ℂ} (hγ : Continuous γ) {a b : ℝ} {z : ℂ}
    (hz : ∀ θ ∈ Icc a b, γ θ ≠ z) : ∃ d > 0, ∀ θ ∈ Icc a b, d ≤ ‖γ θ - z‖ := by
  rcases (Icc a b).eq_empty_or_nonempty with he | hne
  exact ⟨1, one_pos, by simp_all⟩
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    ((hγ.sub continuous_const).norm.continuousOn)
  refine ⟨‖γ θ₀ - z‖, norm_pos_iff.mpr (sub_ne_zero.mpr (hz θ₀ hθ₀)), fun θ hθ => ?_⟩
  tauto

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {a b : ℝ} (hab : a ≤ b) {z : ℂ} (hz : ∀ θ ∈ Icc a b, γ θ ≠ z)
include γ K hK a b hab z hz

/-- The integrand `γ'/(γ - z)` is interval integrable where the curve avoids `z`. -/
lemma intervalIntegrable_deriv_div  :
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
lemma exp_neg_integral_mul_eq :
    ∀ θ ∈ Icc a b,
      Complex.exp (-∫ t in a..θ, deriv γ t / (γ t - z)) * (γ θ - z) = γ a - z := by
  let f (t : ℝ) := deriv γ t / (γ t - z)
  let H (t : ℝ) := ∫ u in a..t, f u
  have hi : IntervalIntegrable f volume a b := intervalIntegrable_deriv_div hK hab hz
  have ha : AbsolutelyContinuousOnInterval H a b :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hi left_mem_uIcc
  obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn ha.continuousOn
  have he : AbsolutelyContinuousOnInterval (fun t => Complex.exp (-H t)) a b :=
    (lipschitzOnWith_cexp_closedBall R).comp_absolutelyContinuousOnInterval
      (fun t ht => by simpa [mem_closedBall_zero_iff] using hR t ht) ha.neg
  have hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt (fun t => Complex.exp (-H t) * (γ t - z)) 0 t := by
    filter_upwards [hi.ae_hasDerivAt_integral, hK.ae_differentiableAt_real] with t h1 h2 ht
    have hh : HasDerivAt H (f t) t := h1 ht _ left_mem_uIcc
    have hne := sub_ne_zero.mpr (hz t (uIcc_of_le hab ▸ ht))
    convert (hh.neg.cexp).mul (h2.hasDerivAt.sub_const z) using 1
    dsimp [f]
    field_simp
    ring
  obtain ⟨C, hC⟩ := (he.smul (hK.sub (LipschitzWith.const z)).lipschitzOnWith.absolutelyContinuousOnInterval).const_of_ae_hasDerivAt_zero hd
  intro θ hθ
  simpa [H, f] using (hC θ (uIcc_of_le hab ▸ hθ)).trans (hC a left_mem_uIcc).symm

end

instance : DiscreteTopology (range ((↑) : ℤ → ℂ)) :=
  Complex.isometry_intCast.isEmbedding.toHomeomorph.symm.isEmbedding.discreteTopology

private lemma mem_range_intCast_of_exp_eq_one {w : ℂ} (h : Complex.exp w = 1) :
    w / (2 * π * Complex.I) ∈ range ((↑) : ℤ → ℂ) := by
  obtain ⟨n, rfl⟩ := Complex.exp_eq_one_iff.mp h
  exact ⟨n, by simp [Real.pi_ne_zero, Complex.I_ne_zero]⟩

/-- The derivative integral computes the increment of any continuous logarithmic lift. -/
lemma integral_deriv_div_eq_lift {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) {z c : ℂ} (hc : c ≠ 0)
    {G : ℝ → ℂ} (hG : ContinuousOn G (Icc a b))
    (hexp : ∀ θ ∈ Icc a b, Complex.exp (G θ) = c * (γ θ - z)) :
    ∫ t in a..b, deriv γ t / (γ t - z) = G b - G a := by
  have hz : ∀ θ ∈ Icc a b, γ θ ≠ z := by
    intro θ hθ heq
    exact Complex.exp_ne_zero _ ((hexp θ hθ).trans (by simp [heq]))
  let H (t : ℝ) := ∫ u in a..t, deriv γ u / (γ u - z)
  have hH : ContinuousOn H (Icc a b) := by
    rw [← uIcc_of_le hab]
    exact (absolutelyContinuousOnInterval_intervalIntegral_banach
      (intervalIntegrable_deriv_div hK hab hz) left_mem_uIcc).continuousOn
  let D (t : ℝ) := (G t - H t - G a) / (2 * π * Complex.I)
  have hD : MapsTo D (Icc a b) (range ((↑) : ℤ → ℂ)) := by
    intro t ht
    apply mem_range_intCast_of_exp_eq_one
    have hn := sub_ne_zero.mpr (hz a (left_mem_Icc.mpr hab))
    rw [Complex.exp_sub, sub_eq_add_neg, Complex.exp_add, hexp t ht, hexp a (left_mem_Icc.mpr hab)]
    have he : Complex.exp (-H t) * (γ t - z) = γ a - z :=
      exp_neg_integral_mul_eq hK hab hz t ht
    rw [mul_assoc, mul_comm (γ t - z), he, div_self (mul_ne_zero hc hn)]
  have h := isPreconnected_Icc.constant_of_mapsTo (isDiscrete_iff_discreteTopology.mpr inferInstance)
    (((hG.sub hH).sub continuousOn_const).div_const (2 * π * Complex.I)) hD
    (right_mem_Icc.mpr hab) (left_mem_Icc.mpr hab)
  change D b = D a at h
  have h0 : D a = 0 := by simp [D, H]
  have hn : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [h0] at h
  dsimp [D] at h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · dsimp [H] at h
    linear_combination -h
  · exact (hn h).elim

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
include γ K hK

/-- The winding number of a closed Lipschitz curve about a point off the curve is an
integer. -/
theorem windingNumber_mem_range_intCast 
    (hclosed : γ (2 * π) = γ 0) {z : ℂ} (hz : z ∉ γ '' Icc 0 (2 * π)) :
    windingNumber γ z ∈ range ((↑) : ℤ → ℂ) := by
  have hp : (0 : ℝ) ≤ 2 * π := by positivity
  have hne : ∀ x ∈ Icc 0 (2 * π), γ x ≠ z := fun x hx he => hz ⟨x, hx, he⟩
  have he := exp_neg_integral_mul_eq hK hp hne (2 * π) ⟨hp, le_rfl⟩
  rw [hclosed] at he
  have h0 := sub_ne_zero.mpr (hne 0 ⟨le_rfl, hp⟩)
  have h1 := mul_right_cancel₀ h0 (he.trans (one_mul _).symm)
  rw [Complex.exp_neg, inv_eq_one] at h1
  simpa only [windingNumber, div_eq_inv_mul] using mem_range_intCast_of_exp_eq_one h1

/-- The derivative integral is continuous in the pole away from the curve. -/
lemma continuousAt_integral_deriv_div {a b : ℝ} (hab : a ≤ b) {z₀ : ℂ}
    (hz₀ : ∀ θ ∈ Icc a b, γ θ ≠ z₀) :
    ContinuousAt (fun z => ∫ θ in a..b, deriv γ θ / (γ θ - z)) z₀ := by
  obtain ⟨ε, hε, hd⟩ := exists_pos_le_norm_sub hK.continuous hz₀
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => K / (ε / 2))
    ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun z => ((measurable_deriv γ).div
      (hK.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds z₀ (half_pos hε)] with z hz
    refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    rw [norm_div]
    refine div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) (half_pos hε) ?_
    have h := norm_sub_norm_le (γ θ - z₀) (z - z₀)
    rw [show γ θ - z₀ - (z - z₀) = γ θ - z by abel] at h
    linarith [hd θ ⟨hθ.1.le, hθ.2⟩, mem_ball_iff_norm.mp hz]
  · refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    have hn := sub_ne_zero.mpr (hz₀ θ ⟨hθ.1.le, hθ.2⟩)
    fun_prop

/-- The winding number is continuous off the curve. -/
theorem continuousOn_windingNumber :
    ContinuousOn (windingNumber γ) (γ '' Icc 0 (2 * π))ᶜ := by
  intro z hz
  exact (continuousAt_const.mul (continuousAt_integral_deriv_div hK (by positivity)
    (fun θ hθ he => hz ⟨θ, hθ, he⟩))).continuousWithinAt

/-- `|wind(γ, z)| ≤ K / dist(z, γ)`: if every point of the curve is at distance at least
`d > K` from `z`, the winding number is `0` (for a closed curve). -/
theorem windingNumber_eq_zero_of_far 
    (hclosed : γ (2 * π) = γ 0) {z : ℂ} {d : ℝ} (hd : (K : ℝ) < d)
    (hzd : ∀ θ ∈ Icc 0 (2 * π), d ≤ ‖γ θ - z‖) : windingNumber γ z = 0 := by
  have hd0 := lt_of_le_of_lt K.coe_nonneg hd
  have hz : z ∉ γ '' Icc 0 (2 * π) := by
    rintro ⟨θ, hθ, rfl⟩
    grind [sub_self, norm_zero]
  obtain ⟨n, hn⟩ := windingNumber_mem_range_intCast hK hclosed hz
  have hbound : ‖windingNumber γ z‖ < 1 := by
    have hint : ‖∫ θ in (0 : ℝ)..(2 * π), deriv γ θ / (γ θ - z)‖ ≤ K / d * |2 * π - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
      rw [uIoc_of_le (by positivity)] at hθ
      have h1 := hzd θ ⟨hθ.1.le, hθ.2⟩
      rw [norm_div]
      exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) hd0 h1
    rw [windingNumber, norm_mul, norm_inv]
    have h2pi : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
      simp
    rw [h2pi, sub_zero, abs_of_pos (by positivity)] at *
    calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * π), deriv γ θ / (γ θ - z)‖
        ≤ (2 * π)⁻¹ * (K / d * (2 * π)) := by gcongr
      _ = K / d := by field_simp
      _ < 1 := (div_lt_one hd0).mpr hd
  rw [← hn] at hbound ⊢
  have : |(n : ℝ)| < 1 := by
    exact_mod_cast hbound
  have h1 : |n| < 1 := by
    rw [← Int.cast_abs] at this; exact_mod_cast this
  simp_all

end

/-- The winding number of a closed Lipschitz curve is constant on every preconnected set
avoiding the curve. -/
theorem windingNumber_const_of_isPreconnected {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {S : Set ℂ} (hS : IsPreconnected S)
    (hSγ : Disjoint S (γ '' Icc 0 (2 * π))) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    windingNumber γ z = windingNumber γ w := by
  have hsub : S ⊆ (γ '' Icc 0 (2 * π))ᶜ := fun x hx h => disjoint_left.mp hSγ hx h
  exact hS.constant_of_mapsTo (isDiscrete_iff_discreteTopology.mpr inferInstance)
    ((continuousOn_windingNumber hK).mono hsub)
    (fun x hx => windingNumber_mem_range_intCast hK hclosed (hsub hx)) hz hw

end PolyaNeumann

end
