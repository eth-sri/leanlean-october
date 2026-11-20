module

public import Mathlib.Analysis.Complex.CoveringMap
public import RequestProject.WindingNumber
public import RequestProject.PlanarNotation

/-!
# The jump of the winding number across a curve

For a closed Lipschitz curve `γ` that passes through `0` at `θ = 0`, whose arc
`γ([-η, η])` is injective and lies on a graph `Im w = f(Re w)`, and which stays away from `0`
on the rest of the period, the winding numbers at `is` and `-is` differ by `±1` in the limit
`s → 0⁺` (`windingNumber_jump`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- Continuous lifts through the exponential that agree at one point agree on a connected set. -/
lemma eqOn_of_exp_eq {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s)
    {F G : X → ℂ} (hF : ContinuousOn F s) (hG : ContinuousOn G s)
    (he : ∀ x ∈ s, Complex.exp (F x) = Complex.exp (G x)) {a} (ha : a ∈ s)
    (h : F a = G a) : EqOn F G s :=
  Complex.isCoveringMap_exp.eqOn_of_comp_eqOn hs hF hG (fun _ hx => Subtype.ext (he _ hx)) ha h

/-- On an arc, the integral of the logarithmic derivative is the increment of any logarithm. -/
lemma integral_deriv_div_eq_lift_sub {γ G : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) {z c : ℂ} (hG : ContinuousOn G (Icc a b))
    (he : ∀ θ ∈ Icc a b, Complex.exp (G θ) = c * (γ θ - z)) :
    ∫ t in a..b, deriv γ t / (γ t - z) = G b - G a := by
  have hz : ∀ θ ∈ Icc a b, γ θ ≠ z := fun θ h h' =>
    Complex.exp_ne_zero (G θ) (by simpa [h'] using he θ h)
  let P := fun x => ∫ t in a..x, deriv γ t / (γ t - z)
  have hP : ContinuousOn P (Icc a b) := uIcc_of_le hab ▸
    intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_deriv_div hK hab hz) left_mem_uIcc
  have ha := left_mem_Icc.mpr hab
  have heq : EqOn (fun x => G x - P x) (fun _ => G a) (Icc a b) := by
    refine eqOn_of_exp_eq isPreconnected_Icc (hG.sub hP) continuousOn_const ?_ ha (by simp [P])
    intro x hx
    rw [sub_eq_add_neg, Complex.exp_add, he x hx, he a ha,
      mul_assoc, mul_comm (γ x - z), exp_neg_integral_mul_eq hK hab hz x hx]
  have hb : G b - P b = G a := heq (right_mem_Icc.mpr hab)
  change P b = _
  linear_combination -hb

/-- Along an arc on which `c (γ - z)` stays in the slit plane, the integral of `γ'/(γ - z)` is
the increment of the branch `log (c (· - z))`. -/
lemma integral_deriv_div_eq_log_sub {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) {z c : ℂ}
    (hslit : ∀ θ ∈ Icc a b, c * (γ θ - z) ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv γ t / (γ t - z) =
      Complex.log (c * (γ b - z)) - Complex.log (c * (γ a - z)) := by
  apply integral_deriv_div_eq_lift_sub hK hab (c := c)
  · exact (continuousOn_const.mul (hK.continuous.sub continuous_const).continuousOn).clog hslit
  · exact fun θ hθ => Complex.exp_log (Complex.slitPlane_ne_zero (hslit θ hθ))

/-- The two branches `log (i u)` and `log (-i u)` differ by `πi` on the right half-plane. -/
lemma log_I_mul_sub_log_neg_I_mul_of_re_pos {u : ℂ} (hu : 0 < u.re) :
    Complex.log (Complex.I * u) - Complex.log (-Complex.I * u) = π * Complex.I := by
  
  rw [neg_mul, Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simpa using hu)]
  push_cast
  ring

/-- The two branches `log (i u)` and `log (-i u)` differ by `-πi` on the left half-plane. -/
lemma log_I_mul_sub_log_neg_I_mul_of_re_neg {u : ℂ} (hu : u.re < 0) :
    Complex.log (Complex.I * u) - Complex.log (-Complex.I * u) = -(π * Complex.I) := by
  
  rw [neg_mul, Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hu)]
  push_cast
  ring

/-- An injective arc on a graph through `0` has endpoints on opposite sides of the vertical
axis. -/
lemma re_mul_re_neg_of_graph {γ : ℝ → ℂ} (hγ : Continuous γ) {η : ℝ} (hη0 : 0 < η)
    {f : ℝ → ℝ} (h0 : γ 0 = 0) (hgraph : ∀ θ ∈ Icc (-η) η, (γ θ).im = f (γ θ).re)
    (hinj : InjOn γ (Icc (-η) η)) : (γ (-η)).re * (γ η).re < 0 := by
  
  let v₀ := Icc (-η) η
  have hc : ContinuousOn (fun θ => (γ θ).re) (v₀) :=
    (Complex.continuous_re.comp hγ).continuousOn
  have hm0 : 0 ∈ v₀ := (by grind)
  have hl : -η ∈ v₀ := (by grind)
  have hr : η ∈ v₀ := (by grind)
  rcases hc.strictMonoOn_of_injOn_Icc' (by linarith) (by
    intro θ₁ h₁ θ₂ h₂ he
    
    exact hinj h₁ h₂ (Complex.ext he (by simp [*]))) with hm | hm
  · have h1 := hm hl hm0 (by linarith)
    have h2 := hm hm0 hr hη0
    simp [h0] at h1 h2
    nlinarith
  · have h1 := hm hl hm0 (by linarith)
    have h2 := hm hm0 hr hη0
    simp [h0] at h1 h2
    nlinarith

/-- The integral of `γ'/(γ - z)` over an arc avoiding `0` is continuous in `z` at `0`. -/
lemma continuousAt_integral_deriv_div {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) (hfar : ∀ θ ∈ Icc a b, γ θ ≠ 0) :
    ContinuousAt (fun z => ∫ θ in a..b, deriv γ θ / (γ θ - z)) 0 := by
  obtain ⟨ε, hε, hd⟩ := exists_pos_le_norm_sub hK.continuous hfar
  have hfar' : ∀ z ∈ ball 0 (ε / 2), ∀ θ ∈ Icc a b, ε / 2 ≤ ‖γ θ - z‖ := by
    intro z hz θ hθ
    grind [hd θ hθ, mem_ball_zero_iff.mp hz, norm_sub_norm_le (γ θ) z]
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => K / (ε / 2))
    ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun z => ((measurable_deriv γ).div
      (hK.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds 0 (half_pos hε)] with z hz
    refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    rw [norm_div]
    exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) (half_pos hε)
      (by grind)
  · refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    have hne : γ θ - 0 ≠ 0 := by rw [sub_zero]; exact hfar θ ⟨hθ.1.le, hθ.2⟩
    fun_prop

/-- For a `2π`-periodic Lipschitz curve avoiding `z` on `[a, a + 2π]`, the winding number
splits at any intermediate point. -/
lemma windingNumber_eq_split {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ anglePeriod) {a m : ℝ} (ham : a ≤ m) (hm : m ≤ a + anglePeriod) {z : ℂ}
    (hz : ∀ θ ∈ Icc a (a + anglePeriod), γ θ ≠ z) :
    windingNumber γ z = (anglePeriod * Complex.I)⁻¹ *
      ((∫ θ in a..m, deriv γ θ / (γ θ - z)) + ∫ θ in m..(a + anglePeriod), deriv γ θ / (γ θ - z)) := by
  have hdper : Function.Periodic (deriv γ) anglePeriod := by
    intro θ
    
    rw [← deriv_comp_add_const, (funext hper)]
  have hgp : Function.Periodic (fun θ => deriv γ θ / (γ θ - z)) anglePeriod := by
    intro θ; simp [hdper θ, hper θ]
  rw [windingNumber]
  congr 1
  have := hgp.intervalIntegral_add_eq 0 a
  rw [zero_add] at this
  rw [this, intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_deriv_div hK ham (by grind))
    (intervalIntegrable_deriv_div hK hm (by grind))]

/-- Continuity of a logarithm branch along a vertical approach. -/
lemma tendsto_log_mul_sub {c w e : ℂ} (h : c * w ∈ Complex.slitPlane) :
    Tendsto (fun s : ℝ => Complex.log (c * (w - s * e))) (𝓝[>] 0)
      (𝓝 (Complex.log (c * w))) := by
  have hc : Continuous (fun s : ℝ => c * (w - s * e)) := by fun_prop
  have := (continuousAt_clog h).tendsto.comp (hc.tendsto' 0 _ (by simp))
  exact tendsto_nhdsWithin_of_tendsto_nhds this

/-- **Jump of the winding number.** Let `γ` be a `2π`-periodic Lipschitz curve with
`γ(0) = 0`, injective on `[-η, η]` (`0 < η < π`), with `γ([-η, η])` contained in a graph
`Im w = f(Re w)`, and `γ(θ) ≠ 0` for `θ ∈ [η, 2π - η]`. Then
`wind(γ, is) - wind(γ, -is) → σ` as `s → 0⁺` for some `σ = ±1`. -/
theorem windingNumber_jump {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ anglePeriod) {η : ℝ} (hη0 : 0 < η) (hηπ : η < π)
    {f : ℝ → ℝ} (h0 : γ 0 = 0) (hgraph : ∀ θ ∈ Icc (-η) η, (γ θ).im = f (γ θ).re)
    (hinj : InjOn γ (Icc (-η) η)) (hfar : ∀ θ ∈ Icc η (anglePeriod - η), γ θ ≠ 0) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      Tendsto (fun s : ℝ => windingNumber γ (s * Complex.I) -
        windingNumber γ (-(s * Complex.I))) (𝓝[>] 0) (𝓝 σ) := by
  have hηη : -η ≤ η := by linarith
  have hm2 : η ≤ -η + anglePeriod := by linarith
  have hfar' : ∀ θ ∈ Icc η (-η + anglePeriod), γ θ ≠ 0 := (by grind)
  obtain ⟨d, hd, hdfar⟩ := exists_pos_le_norm_sub hK.continuous hfar'
  have hf0 : f 0 = 0 := by
    have := hgraph 0 ⟨by linarith, hη0.le⟩
    simpa [h0] using this.symm
  set α := γ (-η) 
  set β := γ η 
  have hαβ  := re_mul_re_neg_of_graph hK.continuous hη0 h0 hgraph hinj
  have hαne : α.re ≠ 0 := fun h => by rw [h, zero_mul] at hαβ; exact lt_irrefl _ hαβ
  have hβne : β.re ≠ 0 := fun h => by rw [h, mul_zero] at hαβ; exact lt_irrefl _ hαβ
  set N  := fun z => ∫ θ in (-η)..η, deriv γ θ / (γ θ - z) 
  set F  := fun z => ∫ θ in η..(-η + anglePeriod), deriv γ θ / (γ θ - z) 
  have hslitP : ∀ s : ℝ, 0 < s → ∀ θ ∈ Icc (-η) η,
      Complex.I * (γ θ - s * Complex.I) ∈ Complex.slitPlane := by
    intro s hs θ hθ
    rw [Complex.mem_slitPlane_iff]
    by_cases hx : (γ θ).re = 0
    · simp [*]
    · simp [*]
  have hslitN : ∀ s : ℝ, 0 < s → ∀ θ ∈ Icc (-η) η,
      -Complex.I * (γ θ - -(s * Complex.I)) ∈ Complex.slitPlane := by
    intro s hs θ hθ
    rw [Complex.mem_slitPlane_iff]
    by_cases hx : (γ θ).re = 0
    · simp [*]
    · simp [*]
  have hnearP : ∀ s : ℝ, 0 < s → N (s * Complex.I) =
      Complex.log (Complex.I * (β - s * Complex.I)) -
        Complex.log (Complex.I * (α - s * Complex.I)) := fun s hs =>
    integral_deriv_div_eq_log_sub hK hηη (hslitP s hs)
  have hnearN : ∀ s : ℝ, 0 < s → N (-(s * Complex.I)) =
      Complex.log (-Complex.I * (β - -(s * Complex.I))) -
        Complex.log (-Complex.I * (α - -(s * Complex.I))) := fun s hs =>
    integral_deriv_div_eq_log_sub hK hηη (hslitN s hs)
  have hav : ∀ s : ℝ, 0 < s → s < d → ∀ z : ℂ, ‖z‖ = s →
      (∀ θ ∈ Icc (-η) η, γ θ ≠ z) → ∀ θ ∈ Icc (-η) (-η + anglePeriod), γ θ ≠ z := by
    grind
  have hneP : ∀ s : ℝ, 0 < s → ∀ θ ∈ Icc (-η) η, γ θ ≠ s * Complex.I := by
    intro s hs θ hθ h
    have := hslitP s hs θ hθ
    rw [h, sub_self, mul_zero] at this
    exact Complex.slitPlane_ne_zero this rfl
  have hneN : ∀ s : ℝ, 0 < s → ∀ θ ∈ Icc (-η) η, γ θ ≠ -(s * Complex.I) := by
    intro s hs θ hθ h
    have := hslitN s hs θ hθ
    rw [h, sub_self, mul_zero] at this
    exact Complex.slitPlane_ne_zero this rfl
  have hnormP : ∀ s : ℝ, 0 < s → ‖(s : ℂ) * Complex.I‖ = s := fun s hs => by
    simp [abs_of_pos hs]
  have hnormN : ∀ s : ℝ, 0 < s → ‖-((s : ℂ) * Complex.I)‖ = s := fun s hs => by
    simp [abs_of_pos hs]
  have heq : ∀ᶠ s : ℝ in 𝓝[>] 0, windingNumber γ (s * Complex.I) -
      windingNumber γ (-(s * Complex.I)) = (anglePeriod * Complex.I)⁻¹ *
        ((N (s * Complex.I) - N (-(s * Complex.I))) +
          (F (s * Complex.I) - F (-(s * Complex.I)))) := by
    filter_upwards [Ioo_mem_nhdsGT hd] with s hs
    rw [windingNumber_eq_split hK hper hηη hm2
        (hav s hs.1 hs.2 _ (hnormP s hs.1) (hneP s hs.1)),
      windingNumber_eq_split hK hper hηη hm2
        (hav s hs.1 hs.2 _ (hnormN s hs.1) (hneN s hs.1))]
    ring
  
  
  
  
  have hNlim : Tendsto (fun s : ℝ => N (s * Complex.I) - N (-(s * Complex.I))) (𝓝[>] 0)
      (𝓝 ((Complex.log (Complex.I * β) - Complex.log (Complex.I * α)) -
        (Complex.log (-Complex.I * β) - Complex.log (-Complex.I * α)))) := by
    have e : (fun s : ℝ => (Complex.log (Complex.I * (β - s * Complex.I)) -
          Complex.log (Complex.I * (α - s * Complex.I))) -
        (Complex.log (-Complex.I * (β - s * -Complex.I)) -
          Complex.log (-Complex.I * (α - s * -Complex.I)))) =ᶠ[𝓝[>] 0]
        fun s : ℝ => N (s * Complex.I) - N (-(s * Complex.I)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [hnearP s hs, hnearN s hs, mul_neg]
    exact Tendsto.congr' e (((tendsto_log_mul_sub (by
        rw [Complex.mem_slitPlane_iff]; right; simpa using hβne)).sub (tendsto_log_mul_sub (by
        rw [Complex.mem_slitPlane_iff]; right; simpa using hαne))).sub
      ((tendsto_log_mul_sub (by
          rw [Complex.mem_slitPlane_iff]; right; simpa using hβne)).sub (tendsto_log_mul_sub (by
          rw [Complex.mem_slitPlane_iff]; right; simpa using hαne))))
  have hFc  := continuousAt_integral_deriv_div hK hm2 hfar'
  have hFlim : Tendsto (fun s : ℝ => F (s * Complex.I) - F (-(s * Complex.I))) (𝓝[>] 0)
      (𝓝 (F 0 - F 0)) := by
    have h1 : Tendsto (fun s : ℝ => (s : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds
        ((Complex.continuous_ofReal.mul continuous_const).tendsto' 0 0 (by simp))
    
    refine (hFc.tendsto.comp h1).sub (hFc.tendsto.comp ?_)
    simpa using h1.neg
  
  have hlim' := ((tendsto_const_nhds (x := (anglePeriod * Complex.I)⁻¹)).mul (hNlim.add hFlim)).congr' (EventuallyEq.symm heq)
  
  rcases lt_or_gt_of_ne hαne with hαneg | hαpos
  · 
    refine ⟨1, Or.inl rfl, ?_⟩
    convert hlim' using 2
    rw [sub_self, add_zero, show ∀ a b c e : ℂ, (a - b) - (c - e) = (a - c) - (b - e) by
      grind, log_I_mul_sub_log_neg_I_mul_of_re_pos (by nlinarith),
      log_I_mul_sub_log_neg_I_mul_of_re_neg hαneg]
    field_simp
    ring
  · 
    refine ⟨-1, Or.inr rfl, ?_⟩
    convert hlim' using 2
    rw [sub_self, add_zero, show ∀ a b c e : ℂ, (a - b) - (c - e) = (a - c) - (b - e) by
      grind, log_I_mul_sub_log_neg_I_mul_of_re_neg (by nlinarith),
      log_I_mul_sub_log_neg_I_mul_of_re_pos hαpos]
    field_simp
    ring

end PolyaNeumann

end
