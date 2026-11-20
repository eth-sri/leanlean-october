module

public import RequestProject.WindingNumber

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

/-- Along an arc on which `c (γ - z)` stays in the slit plane, the integral of `γ'/(γ - z)` is
the increment of the branch `log (c (· - z))`. -/
lemma integral_deriv_div_eq_log_sub {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) {z c : ℂ} (hc : c ≠ 0)
    (hslit : ∀ θ ∈ Icc a b, c * (γ θ - z) ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv γ t / (γ t - z) =
      Complex.log (c * (γ b - z)) - Complex.log (c * (γ a - z)) := by
  refine integral_deriv_div_eq_lift hK hab hc (G := fun θ => Complex.log (c * (γ θ - z))) ?_ ?_
  · exact fun θ hθ => ContinuousAt.comp_continuousWithinAt (g := Complex.log)
      (f := fun t => c * (γ t - z)) (continuousAt_clog (hslit θ hθ))
      ((continuous_const.mul (hK.continuous.sub continuous_const)).continuousWithinAt)
  · exact fun θ hθ => Complex.exp_log (Complex.slitPlane_ne_zero (hslit θ hθ))

/-- The two branches `log (i u)` and `log (-i u)` differ by `πi` on the right half-plane. -/
lemma log_I_mul_sub_log_neg_I_mul_of_re_pos {u : ℂ} (hu : 0 < u.re) :
    Complex.log (Complex.I * u) - Complex.log (-Complex.I * u) = π * Complex.I := by
  have him : 0 < (Complex.I * u).im := by simpa using hu
  rw [neg_mul, Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]
  push_cast
  ring

/-- The two branches `log (i u)` and `log (-i u)` differ by `-πi` on the left half-plane. -/
lemma log_I_mul_sub_log_neg_I_mul_of_re_neg {u : ℂ} (hu : u.re < 0) :
    Complex.log (Complex.I * u) - Complex.log (-Complex.I * u) = -(π * Complex.I) := by
  have him : (Complex.I * u).im < 0 := by simpa using hu
  rw [neg_mul, Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg him]
  push_cast
  ring

/-- An injective arc on a graph through `0` has endpoints on opposite sides of the vertical
axis. -/
lemma re_mul_re_neg_of_graph {γ : ℝ → ℂ} (hγ : Continuous γ) {η : ℝ} (hη0 : 0 < η)
    {f : ℝ → ℝ} (h0 : γ 0 = 0) (hgraph : ∀ θ ∈ Icc (-η) η, (γ θ).im = f (γ θ).re)
    (hinj : InjOn γ (Icc (-η) η)) : (γ (-η)).re * (γ η).re < 0 := by
  have hxinj : InjOn (fun θ => (γ θ).re) (Icc (-η) η) := by
    intro θ₁ h₁ θ₂ h₂ he
    simp  at he
    exact hinj h₁ h₂ (Complex.ext he (by simp_all))
  have hc : ContinuousOn (fun θ => (γ θ).re) (Icc (-η) η) :=
    (Complex.continuous_re.comp hγ).continuousOn
  have hm0 : (0 : ℝ) ∈ Icc (-η) η := ⟨by linarith, hη0.le⟩
  have hl : -η ∈ Icc (-η) η := ⟨le_rfl, by linarith⟩
  have hr : η ∈ Icc (-η) η := ⟨by linarith, le_rfl⟩
  rcases hc.strictMonoOn_of_injOn_Icc' (by linarith) hxinj with hm | hm <;>
    have h₁ := hm hl hm0 (by linarith) <;>
    have h₂ := hm hm0 hr hη0 <;>
    simp [h0] at h₁ h₂ <;> nlinarith

/-- For a `2π`-periodic Lipschitz curve avoiding `z` on `[a, a + 2π]`, the winding number
splits at any intermediate point. -/
lemma windingNumber_eq_split {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ (2 * π)) {a m : ℝ} (ham : a ≤ m) (hm : m ≤ a + 2 * π) {z : ℂ}
    (hz : ∀ θ ∈ Icc a (a + 2 * π), γ θ ≠ z) :
    windingNumber γ z = (2 * π * Complex.I)⁻¹ *
      ((∫ θ in a..m, deriv γ θ / (γ θ - z)) + ∫ θ in m..(a + 2 * π), deriv γ θ / (γ θ - z)) := by
  have hdper : Function.Periodic (deriv γ) (2 * π) := by
    intro θ
    have h1 := funext hper
    rw [← deriv_comp_add_const, h1]
  have hgp : Function.Periodic (fun θ => deriv γ θ / (γ θ - z)) (2 * π) := by
    simp_all
  rw [windingNumber]
  congr 1
  have := hgp.intervalIntegral_add_eq 0 a
  rw [zero_add] at this
  rw [this, intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_deriv_div hK ham fun θ hθ => hz θ ⟨hθ.1, hθ.2.trans hm⟩)
    (intervalIntegrable_deriv_div hK hm fun θ hθ => hz θ ⟨ham.trans hθ.1, hθ.2⟩)]

/-- Continuity of a logarithm branch along a vertical approach. -/
lemma tendsto_log_mul_sub {c w e : ℂ} (h : c * w ∈ Complex.slitPlane) :
    Tendsto (fun s : ℝ => Complex.log (c * (w - s * e))) (𝓝[>] 0)
      (𝓝 (Complex.log (c * w))) := by
  have hc : Continuous (fun s : ℝ => c * (w - (s : ℂ) * e)) := by fun_prop
  have := (continuousAt_clog h).tendsto.comp (hc.tendsto' 0 (c * w) (by simp))
  exact tendsto_nhdsWithin_of_tendsto_nhds this

/-- **Jump of the winding number.** Let `γ` be a `2π`-periodic Lipschitz curve with
`γ(0) = 0`, injective on `[-η, η]` (`0 < η < π`), with `γ([-η, η])` contained in a graph
`Im w = f(Re w)`, and `γ(θ) ≠ 0` for `θ ∈ [η, 2π - η]`. Then
`wind(γ, is) - wind(γ, -is) → σ` as `s → 0⁺` for some `σ = ±1`. -/
theorem windingNumber_jump {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ (2 * π)) {η : ℝ} (hη0 : 0 < η) (hηπ : η < π)
    {f : ℝ → ℝ} (h0 : γ 0 = 0) (hgraph : ∀ θ ∈ Icc (-η) η, (γ θ).im = f (γ θ).re)
    (hinj : InjOn γ (Icc (-η) η)) (hfar : ∀ θ ∈ Icc η (2 * π - η), γ θ ≠ 0) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      Tendsto (fun s : ℝ => windingNumber γ (s * Complex.I) -
        windingNumber γ (-(s * Complex.I))) (𝓝[>] 0) (𝓝 σ) := by
  have hηη : -η ≤ η := by linarith
  have hm2 : η ≤ -η + 2 * π := by linarith
  have hfar' : ∀ θ ∈ Icc η (-η + 2 * π), γ θ ≠ 0 := fun θ hθ =>
    hfar θ ⟨hθ.1, by grind⟩
  obtain ⟨d, hd, hdfar⟩ := exists_pos_le_norm_sub hK.continuous hfar'
  have hf0 : f 0 = 0 := by
    have := hgraph 0 ⟨by linarith, hη0.le⟩
    rw [h0] at this
    tauto
  set α := γ (-η) with hα
  set β := γ η with hβ
  have hαβ := re_mul_re_neg_of_graph hK.continuous hη0 h0 hgraph hinj
  have hαne : α.re ≠ 0 := fun h => by rw [h, zero_mul] at hαβ; simp_all
  have hβne : β.re ≠ 0 := fun h => by rw [h, mul_zero] at hαβ; simp_all
  set N : ℂ → ℂ := fun z => ∫ θ in (-η)..η, deriv γ θ / (γ θ - z) with hN
  set F : ℂ → ℂ := fun z => ∫ θ in η..(-η + 2 * π), deriv γ θ / (γ θ - z) with hF
  have hlim (c : ℂ) (hc : c = Complex.I ∨ c = -Complex.I) :
      Tendsto (fun s : ℝ => windingNumber γ (s * c)) (𝓝[>] 0)
        (𝓝 ((2 * π * Complex.I)⁻¹ * (Complex.log (c * β) - Complex.log (c * α) + F 0))) := by
    have hbranch (w : ℂ) (hw : w.re ≠ 0) : c * w ∈ Complex.slitPlane := by
      rcases hc with rfl | rfl <;> exact Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hw))
    have hslit (s : ℝ) (hs : 0 < s) (θ : ℝ) (hθ : θ ∈ Icc (-η) η) :
        c * (γ θ - s * c) ∈ Complex.slitPlane := by
      by_cases hx : (γ θ).re = 0
      · have hy : (γ θ).im = 0 := by rw [hgraph θ hθ, hx, hf0]
        have hz : γ θ = 0 := Complex.ext (by simpa using hx) (by simpa using hy)
        rcases hc with rfl | rfl <;> simp [hz, Complex.mem_slitPlane_iff, Complex.mul_re, hs]
      · apply hbranch
        rcases hc with rfl | rfl <;> simpa [Complex.mul_re] using hx
    have hNlim : Tendsto (fun s : ℝ => N (s * c)) (𝓝[>] 0)
        (𝓝 (Complex.log (c * β) - Complex.log (c * α))) := by
      refine ((tendsto_log_mul_sub (e := c) (hbranch β hβne)).sub
        (tendsto_log_mul_sub (e := c) (hbranch α hαne))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hcn : c ≠ 0 := by rcases hc with rfl | rfl <;> simp
      exact (integral_deriv_div_eq_log_sub hK hηη hcn (hslit s hs)).symm
    have hFc : ContinuousAt F 0 := continuousAt_integral_deriv_div hK hm2 hfar'
    have hs0 : Tendsto (fun s : ℝ => (s : ℂ) * c) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds
        ((Complex.continuous_ofReal.mul continuous_const).tendsto' 0 0 (by simp))
    refine (tendsto_const_nhds.mul (hNlim.add (hFc.tendsto.comp hs0))).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hd] with s hs
    symm
    apply windingNumber_eq_split hK hper hηη hm2
    intro θ hθ heq
    by_cases hθη : θ ≤ η
    · exact Complex.slitPlane_ne_zero (hslit s hs.1 θ ⟨hθ.1, hθη⟩)
        (by rw [heq, sub_self, mul_zero])
    · have h := hdfar θ ⟨le_of_not_ge hθη, hθ.2⟩
      rw [heq, sub_zero] at h
      rcases hc with rfl | rfl <;> simp [abs_of_pos hs.1] at h <;> linarith [hs.2]
  have hlim' := (hlim Complex.I (Or.inl rfl)).sub (hlim (-Complex.I) (Or.inr rfl))
  rw [show ∀ a b c d f k : ℂ, k * (a - b + f) - k * (c - d + f) = k * ((a - c) - (b - d)) by
    intros; ring] at hlim'
  simp only [mul_neg] at hlim'
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by simp
  rcases lt_or_gt_of_ne hαne with hαneg | hαpos
  · have hβpos : 0 < β.re := by nlinarith
    refine ⟨1, Or.inl rfl, ?_⟩
    convert hlim' using 2
    rw [log_I_mul_sub_log_neg_I_mul_of_re_pos hβpos, log_I_mul_sub_log_neg_I_mul_of_re_neg hαneg]
    field_simp
    ring
  · have hβneg : β.re < 0 := by nlinarith
    refine ⟨-1, Or.inr rfl, ?_⟩
    convert hlim' using 2
    rw [log_I_mul_sub_log_neg_I_mul_of_re_neg hβneg, log_I_mul_sub_log_neg_I_mul_of_re_pos hαpos]
    field_simp
    ring

end PolyaNeumann

end
