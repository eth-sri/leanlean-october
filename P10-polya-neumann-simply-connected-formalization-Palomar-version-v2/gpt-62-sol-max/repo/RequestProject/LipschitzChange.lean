module

public import RequestProject.ArcLength
public import RequestProject.CurveContinuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Volume distortion under Lipschitz maps and continuity of the signed-area integral. -/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real Interval ENNReal

noncomputable section

namespace PolyaNeumann

/-- Hausdorff measure is proportional to Lebesgue measure on the plane, so a
`K`-Lipschitz map increases areas by at most `K²`. -/
theorem volume_image_le_of_lipschitzOnWith {f : ℂ → ℂ} {K : NNReal} {s : Set ℂ}
    (hf : LipschitzOnWith K f s) : volume (f '' s) ≤ (K : ℝ≥0∞)^2 * volume s := by
  let μ : Measure ℂ := μH[Module.finrank ℝ ℂ]
  let c := Measure.addHaarScalarFactor μ volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  have hc : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'
  have hle := hf.hausdorffMeasure_image_le (d := Module.finrank ℝ ℂ) (by positivity)
  change μ (f '' s) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ ℂ : ℝ) * μ s at hle
  rw [hμ, Complex.finrank_real_complex] at hle
  simp only [Nat.cast_ofNat, ENNReal.rpow_two, Measure.smul_apply] at hle
  change (c : ℝ≥0∞) * volume (f '' s) ≤ (K : ℝ≥0∞)^2 * ((c : ℝ≥0∞) * volume s) at hle
  exact (ENNReal.mul_le_mul_iff_left hc ENNReal.coe_ne_top).mp
    (by simpa only [mul_comm (c : ℝ≥0∞), mul_assoc] using hle)

/-- A continuous `2π`-periodic function is bounded. -/
lemma exists_bound_of_periodic {β : ℝ → ℂ} (hβ : Continuous β)
    (hp : Function.Periodic β (2 * π)) : ∃ M, ∀ θ, ‖β θ‖ ≤ M := by
  have hc : IsCompact (β '' Icc 0 (0 + 2 * π)) := isCompact_Icc.image hβ
  rw [hp.image_Icc Real.two_pi_pos] at hc
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  tauto

/-- Products of a bounded derivative-type factor and a bounded continuous factor are
interval integrable. -/
lemma intervalIntegrable_conj_mul {f g : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) {A B : ℝ} (hA : ∀ θ, ‖f θ‖ ≤ A) (hB : ∀ θ, ‖g θ‖ ≤ B)
    (a b : ℝ) : IntervalIntegrable (fun θ => conj (f θ) * g θ) volume a b := by
  refine intervalIntegrable_of_bounded
    ((Complex.continuous_conj.comp_aestronglyMeasurable hf).mul hg) (B := A * B)
    (fun θ => ?_) a b
  show ‖conj (f θ) * g θ‖ ≤ A * B
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hA θ) (hB θ) (norm_nonneg _) ((norm_nonneg _).trans (hA θ))

/-- Integration by parts for Lipschitz `2π`-periodic curves:
`∫₀^{2π} conj β · δ' = -∫₀^{2π} conj β' · δ`. -/
lemma integral_conj_mul_deriv_periodic {β δ : ℝ → ℂ} {Kβ Kδ : NNReal}
    (hβ : LipschitzWith Kβ β) (hδ : LipschitzWith Kδ δ)
    (hβp : Function.Periodic β (2 * π)) (hδp : Function.Periodic δ (2 * π)) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (β θ) * deriv δ θ =
      -∫ θ in (0 : ℝ)..(2 * π), conj (deriv β θ) * δ θ := by
  obtain ⟨Mβ, hMβ⟩ := exists_bound_of_periodic hβ.continuous hβp
  obtain ⟨Mδ, hMδ⟩ := exists_bound_of_periodic hδ.continuous hδp
  have hMβ0 := (norm_nonneg _).trans (hMβ 0)
  have hMδ0 := (norm_nonneg _).trans (hMδ 0)
  set P : ℝ → ℂ := fun θ => conj (β θ) * δ θ with hPdef
  have hP : LipschitzWith (Mβ.toNNReal * Kδ + Kβ * Mδ.toNNReal) P := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := hδ.dist_le_mul x y
    have h2 := hβ.dist_le_mul x y
    rw [dist_eq_norm] at h1 h2 ⊢
    have e : P x - P y = conj (β x) * (δ x - δ y) + conj (β x - β y) * δ y := by
      grind
    rw [e]
    push_cast
    rw [Real.coe_toNNReal _ hMβ0, Real.coe_toNNReal _ hMδ0]
    calc ‖conj (β x) * (δ x - δ y) + conj (β x - β y) * δ y‖
        ≤ ‖β x‖ * ‖δ x - δ y‖ + ‖β x - β y‖ * ‖δ y‖ := by
          refine (norm_add_le _ _).trans ?_
          grind [norm_mul, Complex.norm_conj]
      _ ≤ Mβ * (Kδ * dist x y) + Kβ * dist x y * Mδ := by
          gcongr
          all_goals tauto
      _ = (Mβ * Kδ + Kβ * Mδ) * dist x y := by ring
  have hderiv : ∀ᵐ θ, θ ∈ Ι (0 : ℝ) (2 * π) →
      deriv P θ = conj (deriv β θ) * δ θ + conj (β θ) * deriv δ θ := by
    filter_upwards [hβ.ae_differentiableAt (μ := volume),
      hδ.ae_differentiableAt (μ := volume)] with θ h1 h2 _
    exact (h1.hasDerivAt.star.mul h2.hasDerivAt).deriv
  have hFTC := integral_deriv_of_lipschitz hP 0 (2 * π)
  rw [intervalIntegral.integral_congr_ae hderiv,
    intervalIntegral.integral_add
      (intervalIntegrable_conj_mul (measurable_deriv β).aestronglyMeasurable
        hδ.continuous.aestronglyMeasurable (fun _ => norm_deriv_le_of_lipschitz hβ) hMδ _ _)
      (intervalIntegrable_conj_mul hβ.continuous.aestronglyMeasurable
        (measurable_deriv δ).aestronglyMeasurable hMβ (fun _ => norm_deriv_le_of_lipschitz hδ) _ _)] at hFTC
  have hP2 : P (2 * π) = P 0 := by
    simp  [hPdef]; rw [show (2 * π : ℝ) = 0 + 2 * π by ring, hβp, hδp]
  rw [hP2, sub_self] at hFTC
  linear_combination hFTC

/-- Continuity of the signed-area integral under uniform convergence of uniformly Lipschitz
periodic curves. -/
theorem tendsto_integral_signedAreaDensity {α : ℕ → ℝ → ℂ} {β : ℝ → ℂ} {K : NNReal}
    (hα : ∀ n, LipschitzWith K (α n)) (hβ : LipschitzWith K β)
    (hαp : ∀ n, Function.Periodic (α n) (2 * π)) (hβp : Function.Periodic β (2 * π))
    (h : TendstoUniformlyOn α β atTop (Icc 0 (2 * π))) :
    Tendsto (fun n => ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity (α n) θ) atTop
      (𝓝 (∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity β θ)) := by
  have hint : ∀ {γ : ℝ → ℂ} {Kγ : NNReal}, LipschitzWith Kγ γ → Function.Periodic γ (2 * π) →
      IntervalIntegrable (fun θ => conj (γ θ) * deriv γ θ) volume 0 (2 * π) := by
    intro γ Kγ hγ hγp
    obtain ⟨M, hM⟩ := exists_bound_of_periodic hγ.continuous hγp
    exact intervalIntegrable_conj_mul hγ.continuous.aestronglyMeasurable
      (measurable_deriv γ).aestronglyMeasurable hM (fun _ => norm_deriv_le_of_lipschitz hγ) _ _
  have him : ∀ {γ : ℝ → ℂ} {Kγ : NNReal}, LipschitzWith Kγ γ → Function.Periodic γ (2 * π) →
      ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ θ =
        (∫ θ in (0 : ℝ)..(2 * π), conj (γ θ) * deriv γ θ).im := by
    intro γ Kγ hγ hγp
    exact Complex.imCLM.intervalIntegral_comp_comm (hint hγ hγp)
  have e :=
    funext fun n => him (hα n) (hαp n)
  rw [e, him hβ hβp]
  refine (Complex.continuous_im.tendsto _).comp (Metric.tendsto_nhds.mpr fun ε hε => ?_)
  set η := ε / (4 * π * K + 1) with hηdef
  have hη : 0 < η := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h η hη] with n hn
  set δ : ℝ → ℂ := fun θ => α n θ - β θ with hδdef
  have hδL := (hα n).sub hβ
  have hδp : Function.Periodic δ (2 * π) := fun θ => by simp_all
  have hδd : ∀ᵐ θ, θ ∈ Ι (0 : ℝ) (2 * π) →
      conj (α n θ) * deriv (α n) θ - conj (β θ) * deriv β θ =
        conj (δ θ) * deriv (α n) θ + conj (β θ) * deriv δ θ := by
    filter_upwards [(hα n).ae_differentiableAt (μ := volume),
      hβ.ae_differentiableAt (μ := volume)] with θ h1 h2 _
    have hd : deriv δ θ = deriv (α n) θ - deriv β θ := deriv_sub h1 h2
    rw [hd]; simp only [hδdef, map_sub]; ring
  obtain ⟨Mβ, hMβ⟩ := exists_bound_of_periodic hβ.continuous hβp
  obtain ⟨Mδ, hMδ⟩ := exists_bound_of_periodic hδL.continuous hδp
  have i1 : IntervalIntegrable (fun θ => conj (δ θ) * deriv (α n) θ) volume 0 (2 * π) :=
    intervalIntegrable_conj_mul hδL.continuous.aestronglyMeasurable
      (measurable_deriv _).aestronglyMeasurable hMδ (fun _ => norm_deriv_le_of_lipschitz (hα n)) _ _
  have i2 : IntervalIntegrable (fun θ => conj (β θ) * deriv δ θ) volume 0 (2 * π) :=
    intervalIntegrable_conj_mul hβ.continuous.aestronglyMeasurable
      (measurable_deriv _).aestronglyMeasurable hMβ (fun _ => norm_deriv_le_of_lipschitz hδL) _ _
  have key : (∫ θ in (0 : ℝ)..(2 * π), conj (α n θ) * deriv (α n) θ) -
      ∫ θ in (0 : ℝ)..(2 * π), conj (β θ) * deriv β θ =
      (∫ θ in (0 : ℝ)..(2 * π), conj (δ θ) * deriv (α n) θ) -
        ∫ θ in (0 : ℝ)..(2 * π), conj (deriv β θ) * δ θ := by
    rw [← intervalIntegral.integral_sub (hint (hα n) (hαp n)) (hint hβ hβp),
      intervalIntegral.integral_congr_ae hδd, intervalIntegral.integral_add i1 i2,
      integral_conj_mul_deriv_periodic hβ hδL hβp hδp]
    ring
  have hδη : ∀ θ ∈ Ι (0 : ℝ) (2 * π), ‖δ θ‖ ≤ η := by
    intro θ hθ
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ
    have := hn θ (Ioc_subset_Icc_self hθ)
    rw [dist_comm, dist_eq_norm] at this
    gcongr
  have b1 : ‖∫ θ in (0 : ℝ)..(2 * π), conj (δ θ) * deriv (α n) θ‖ ≤ η * K * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hδη θ hθ) (norm_deriv_le_of_lipschitz (hα n)) (norm_nonneg _) hη.le
  have b2 : ‖∫ θ in (0 : ℝ)..(2 * π), conj (deriv β θ) * δ θ‖ ≤ K * η * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (norm_deriv_le_of_lipschitz hβ) (hδη θ hθ) (norm_nonneg _) K.2
  rw [sub_zero, abs_of_pos Real.two_pi_pos] at b1 b2
  have hfin : 4 * π * K * η < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos, K.2]
  rw [dist_eq_norm, key]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ η * K * (2 * π) + K * η * (2 * π) := add_le_add b1 b2
    _ = 4 * π * K * η := by ring
    _ < ε := hfin

end PolyaNeumann

end
