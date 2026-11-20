module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.ArcLength
public import RequestProject.CurveContinuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import RequestProject.PlanarNotation

/-!
# Lipschitz maps of the plane and of closed curves (tools for Section 10)

* `volume_image_eq_zero_of_lipschitzOnWith`: a Lipschitz map of the plane sends null sets to null
  sets;
* `abs_det_le_sq_norm`, `abs_det_fderiv_le`: `|det Df| ≤ ‖Df‖² ≤ K²` for a map that is
  `K`-Lipschitz on an open set;
* `volume_image_eq_lintegral`: change of variables `|f(Ω)| = ∫_Ω |det Df|` for maps that are
  Lipschitz and injective on an open set `Ω` (via Rademacher's theorem);
* `tendsto_integral_signedAreaDensity`: the signed-area integral `∫₀^{2π} Im(conj γ · γ')` is
  continuous under uniform convergence of uniformly Lipschitz `2π`-periodic curves.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real Interval

noncomputable section

namespace PolyaNeumann

/-- Area distortion in the plane. Lebesgue measure is a scalar multiple of
Hausdorff measure in the real dimension two; the normalization cancels. -/
lemma volume_image_le_lipschitz {f : ℂ → ℂ} {K : NNReal} {s : Set ℂ} (hf : LipschitzOnWith K f s) :
    volume (f '' s) ≤ (K : ENNReal)^2 * volume s := by
  let d := Module.finrank ℝ ℂ
  let μ : Measure ℂ := μH[(d : ℝ)]
  have h := hf.hausdorffMeasure_image_le (d := (d : ℝ)) (by positivity)
  have he := Measure.isAddLeftInvariant_eq_smul (volume : Measure ℂ) μ
  rw [he, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]
  apply mul_le_mul_right
  simpa [μ, d, Complex.finrank_real_complex, ENNReal.rpow_natCast] using h

lemma volume_image_eq_zero_of_lipschitzOnWith {f : ℂ → ℂ} {K : NNReal} {s : Set ℂ}
    (hf : LipschitzOnWith K f s) (hs : volume s = 0) : volume (f '' s) = 0 :=
  nonpos_iff_eq_zero.mp (by simpa [hs] using volume_image_le_lipschitz hf)

/-- `|det A| ≤ ‖A‖²` for a real-linear map of the plane. -/
lemma abs_det_le_sq_norm (A : ℂ →L[ℝ] ℂ) : |A.det| ≤ ‖A‖ ^ 2 := by
  have h := volume_image_le_lipschitz (A.lipschitz.lipschitzOnWith (s := Metric.ball (0 : ℂ) 1))
  rw [Measure.addHaar_image_continuousLinearMap] at h
  have hpos := (Metric.measure_ball_pos (μ := (volume : Measure ℂ)) 0 one_pos).ne'
  have hdet := (ENNReal.mul_le_mul_iff_left hpos measure_ball_lt_top.ne).mp h
  apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖A‖)).mp
  rw [ENNReal.ofReal_pow (norm_nonneg A), ← coe_nnnorm A, ENNReal.ofReal_coe_nnreal]
  exact hdet

/-- `|det Df(x)| ≤ K²` at every point of an open set on which `f` is `K`-Lipschitz. -/
lemma abs_det_fderiv_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} {K : NNReal}
    (hf : LipschitzOnWith K f Ω) {x : ℂ} (hx : x ∈ Ω) :
    |(fderiv ℝ f x).det| ≤ (K : ℝ) ^ 2 :=
  (abs_det_le_sq_norm _).trans (pow_le_pow_left₀ (norm_nonneg _)
    (norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hx) hf) 2)

/-- Rademacher leaves a measurable subset on which the derivative exists;
removing the exceptional points changes neither the source nor its image a.e. -/
lemma differentiability_core {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} {K : NNReal}
    (hf : LipschitzOnWith K f Ω) : ∃ s ⊆ Ω, MeasurableSet s ∧ s =ᵐ[volume] Ω ∧
      f '' s =ᵐ[volume] f '' Ω ∧ ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x := by
  let s := Ω ∩ {x | DifferentiableAt ℝ f x}
  have hnull : volume (Ω \ s) = 0 := by
    have h := hf.ae_differentiableWithinAt_of_mem (μ := volume)
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    exact fun x hx hd => hx.2 ⟨hx.1, (hd hx.1).differentiableAt (hΩ.mem_nhds hx.1)⟩
  refine ⟨s, inter_subset_left, hΩ.measurableSet.inter (measurableSet_of_differentiableAt ℝ f),
    ae_eq_set.mpr ⟨by rw [diff_eq_empty.mpr inter_subset_left, measure_empty], hnull⟩, ae_eq_set.mpr ⟨?_, ?_⟩, fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt⟩
  · rw [diff_eq_empty.mpr (image_mono inter_subset_left), measure_empty]
  · refine measure_mono_null ?_ (volume_image_eq_zero_of_lipschitzOnWith (hf.mono diff_subset) hnull)
    rintro _ ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun h => hn ⟨x, h, rfl⟩⟩, rfl⟩

/-- Change of variables for a map that is Lipschitz and injective on an open set:
`|f(Ω)| = ∫_Ω |det Df|`. -/
theorem volume_image_eq_lintegral {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} {K : NNReal}
    (hf : LipschitzOnWith K f Ω) (hinj : InjOn f Ω) :
    volume (f '' Ω) =
      ∫⁻ x in Ω, ENNReal.ofReal |(fderiv ℝ f x).det| := by
  obtain ⟨s, hsub, hs, he, hi, hd⟩ := differentiability_core hΩ hf
  rw [← measure_congr hi, ← setLIntegral_congr he]
  exact (lintegral_abs_det_fderiv_eq_addHaar_image volume hs hd (hinj.mono hsub)).symm

/-- A continuous `2π`-periodic function is bounded. -/
lemma exists_bound_of_periodic {β : ℝ → ℂ} (hβ : Continuous β)
    (hp : Function.Periodic β anglePeriod) : ∃ M, ∀ θ, ‖β θ‖ ≤ M := by
  have hc : IsCompact (β '' Icc 0 (0 + anglePeriod)) := isCompact_Icc.image hβ
  rw [hp.image_Icc Real.two_pi_pos] at hc
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  aesop

/-- Products of a bounded derivative-type factor and a bounded continuous factor are
interval integrable. -/
lemma intervalIntegrable_conj_mul {f g : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) {A B : ℝ} (hA : ∀ θ, ‖f θ‖ ≤ A) (hB : ∀ θ, ‖g θ‖ ≤ B)
    (a b : ℝ) : IntervalIntegrable (fun θ => conj (f θ) * g θ) volume a b := by
  refine intervalIntegrable_of_bounded
    ((by fun_prop)) (B := A * B)
    (fun θ => ?_) a b
  show ‖conj (f θ) * g θ‖ ≤ A * B
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hA θ) (hB θ) (norm_nonneg _) ((norm_nonneg _).trans (hA θ))

/-- Integration by parts for Lipschitz `2π`-periodic curves:
`∫₀^{2π} conj β · δ' = -∫₀^{2π} conj β' · δ`. -/
lemma integral_conj_mul_deriv_periodic {β δ : ℝ → ℂ} {Kβ Kδ : NNReal}
    (hβ : LipschitzWith Kβ β) (hδ : LipschitzWith Kδ δ)
    (hβp : Function.Periodic β anglePeriod) (hδp : Function.Periodic δ anglePeriod) :
    ∫ₚ θ, conj (β θ) * deriv δ θ =
      -∫ₚ θ, conj (deriv β θ) * δ θ := by
  obtain ⟨Mβ, hMβ⟩ := exists_bound_of_periodic hβ.continuous hβp
  obtain ⟨Mδ, hMδ⟩ := exists_bound_of_periodic hδ.continuous hδp
  have hMβ0  := (norm_nonneg _).trans (hMβ 0)
  
  set P : ℝ → ℂ := fun θ => conj (β θ) * δ θ with hPdef
  have hP : LipschitzWith (Mβ.toNNReal * Kδ + Kβ * Mδ.toNNReal) P := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := hδ.dist_le_mul x y
    have h2 := hβ.dist_le_mul x y
    rw [dist_eq_norm] at h1 h2 ⊢
    have e : P x - P y = conj (β x) * (δ x - δ y) + conj (β x - β y) * δ y := by
      simp [hPdef] <;> ring
    rw [e]
    push_cast
    rw [Real.coe_toNNReal _ hMβ0, Real.coe_toNNReal _ ((norm_nonneg _).trans (hMδ 0))]
    calc _
        ≤ ‖β x‖ * ‖δ x - δ y‖ + ‖β x - β y‖ * ‖δ y‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      _ ≤ Mβ * (Kδ * dist x y) + Kβ * dist x y * Mδ := by
          bound
      _ = _ := by ring
  have hderiv : ∀ᵐ θ, θ ∈ Ι (0 : ℝ) anglePeriod →
      deriv P θ = conj (deriv β θ) * δ θ + conj (β θ) * deriv δ θ := by
    filter_upwards [hβ.ae_differentiableAt ,
      hδ.ae_differentiableAt ] with θ h1 h2 _
    exact (h1.hasDerivAt.star.mul h2.hasDerivAt).deriv
  have hFTC := integral_deriv_of_lipschitz hP 0 anglePeriod
  rw [intervalIntegral.integral_congr_ae hderiv,
    intervalIntegral.integral_add
      (intervalIntegrable_conj_mul (by fun_prop)
        hδ.continuous.aestronglyMeasurable (fun _ => norm_deriv_le_of_lipschitz hβ) hMδ _ _)
      (intervalIntegrable_conj_mul hβ.continuous.aestronglyMeasurable
        (by fun_prop) hMβ (fun _ => norm_deriv_le_of_lipschitz hδ) _ _)] at hFTC
  have hP2 : P anglePeriod = P 0 := by
    simp only [hPdef]; rw [show (anglePeriod : ℝ) = 0 + anglePeriod by ring, hβp, hδp]
  rw [hP2, sub_self] at hFTC
  linear_combination hFTC

/-- Continuity of the signed-area integral under uniform convergence of uniformly Lipschitz
periodic curves. -/
theorem tendsto_integral_signedAreaDensity {α : ℕ → ℝ → ℂ} {β : ℝ → ℂ} {K : NNReal}
    (hα : ∀ n, LipschitzWith K (α n)) (hβ : LipschitzWith K β)
    (hαp : ∀ n, Function.Periodic (α n) anglePeriod) (hβp : Function.Periodic β anglePeriod)
    (h : TendstoUniformlyOn α β atTop angleInterval) :
    Tendsto (fun n => ∫ₚ θ, signedAreaDensity (α n) θ) atTop
      (𝓝 (∫ₚ θ, signedAreaDensity β θ)) := by
  have hint : ∀ {γ : ℝ → ℂ} {Kγ : NNReal}, LipschitzWith Kγ γ → Function.Periodic γ anglePeriod →
      IntervalIntegrable (fun θ => conj (γ θ) * deriv γ θ) volume 0 anglePeriod := by
    intro γ Kγ hγ hγp
    obtain ⟨M, hM⟩ := exists_bound_of_periodic hγ.continuous hγp
    exact intervalIntegrable_conj_mul hγ.continuous.aestronglyMeasurable
      (by fun_prop) hM (fun _ => norm_deriv_le_of_lipschitz hγ) _ _
  have him : ∀ {γ : ℝ → ℂ} {Kγ : NNReal}, LipschitzWith Kγ γ → Function.Periodic γ anglePeriod →
      ∫ₚ θ, signedAreaDensity γ θ =
        (∫ₚ θ, conj (γ θ) * deriv γ θ).im := by
    intro γ Kγ hγ hγp
    exact Complex.imCLM.intervalIntegral_comp_comm (hint hγ hγp)
  
  rw [(funext fun n => him (hα n) (hαp n)), him hβ hβp]
  refine (Complex.continuous_im.tendsto _).comp (Metric.tendsto_nhds.mpr fun ε hε => ?_)
  set η := ε / (4 * π * K + 1) with hηdef
  have hη : 0 < η := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h η hη] with n hn
  set δ : ℝ → ℂ := fun θ => α n θ - β θ with hδdef
  have hδL  := (hα n).sub hβ
  have hδp : Function.Periodic δ anglePeriod := fun θ => by simp [hδdef, hαp n θ, hβp θ]
  have hδd : ∀ᵐ θ, θ ∈ Ι 0 anglePeriod →
      conj (α n θ) * deriv (α n) θ - conj (β θ) * deriv β θ =
        conj (δ θ) * deriv (α n) θ + conj (β θ) * deriv δ θ := by
    filter_upwards [(hα n).ae_differentiableAt ,
      hβ.ae_differentiableAt ] with θ h1 h2 _
    have hd : deriv δ θ = deriv (α n) θ - deriv β θ := deriv_sub h1 h2
    rw [hd]; simp [hδdef] <;> ring
  obtain ⟨Mβ, hMβ⟩ := exists_bound_of_periodic hβ.continuous hβp
  obtain ⟨Mδ, hMδ⟩ := exists_bound_of_periodic hδL.continuous hδp
  have i1 : IntervalIntegrable (fun θ => conj (δ θ) * deriv (α n) θ) volume 0 anglePeriod :=
    intervalIntegrable_conj_mul hδL.continuous.aestronglyMeasurable
      (by fun_prop) hMδ (fun _ => norm_deriv_le_of_lipschitz (hα n)) _ _
  have i2 : IntervalIntegrable (fun θ => conj (β θ) * deriv δ θ) volume 0 anglePeriod :=
    intervalIntegrable_conj_mul hβ.continuous.aestronglyMeasurable
      (measurable_deriv _).aestronglyMeasurable hMβ (fun _ => norm_deriv_le_of_lipschitz hδL) _ _
  have key : (∫ₚ θ, conj (α n θ) * deriv (α n) θ) -
      ∫ₚ θ, conj (β θ) * deriv β θ =
      (∫ₚ θ, conj (δ θ) * deriv (α n) θ) -
        ∫ₚ θ, conj (deriv β θ) * δ θ := by
    rw [← intervalIntegral.integral_sub (hint (hα n) (hαp n)) (hint hβ hβp),
      intervalIntegral.integral_congr_ae hδd, intervalIntegral.integral_add i1 i2,
      integral_conj_mul_deriv_periodic hβ hδL hβp hδp]
    ring
  have hδη : ∀ θ ∈ Ι 0 anglePeriod, ‖δ θ‖ ≤ η := by
    intro θ hθ
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ
    have := hn θ (Ioc_subset_Icc_self hθ)
    rw [dist_comm, dist_eq_norm] at this
    exact this.le
  have b1 : ‖∫ₚ θ, conj (δ θ) * deriv (α n) θ‖ ≤ η * K * |anglePeriod - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hδη θ hθ) (norm_deriv_le_of_lipschitz (hα n)) (norm_nonneg _) hη.le
  have b2 : ‖∫ₚ θ, conj (deriv β θ) * δ θ‖ ≤ K * η * |anglePeriod - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (norm_deriv_le_of_lipschitz hβ) (hδη θ hθ) (norm_nonneg _) K.2
  rw [sub_zero, abs_of_pos Real.two_pi_pos] at b1 b2
  
  rw [dist_eq_norm, key]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add b1 b2
    _ = 4 * π * K * η := by ring
    _ < ε := (by
      rw [hηdef, mul_div_assoc', div_lt_iff₀ (by positivity)]
      linarith)

end PolyaNeumann

end
