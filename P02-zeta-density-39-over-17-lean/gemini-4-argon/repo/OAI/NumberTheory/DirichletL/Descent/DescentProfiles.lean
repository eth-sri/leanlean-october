module
public import OAI.NumberTheory.DirichletL.Foundation

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

lemma schwartz_logPhase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  convert schwartz_log_inversion g x using 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  simp only [logPhase, Real.inner_apply]
  congr 1
  push_cast
  ring

theorem descent_profile_identity {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak : ι → ℝ)
    (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (he : ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t : ℝ, (∏ i, V i (y i) * logPhase t (ak i * y i)) * b t) :
    ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
        paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
          (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
            logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) := by
  intro y
  let P : ℂ := ∏ i, V i (y i)
  let x₁ : ℝ := ∑ i, a₁ i * y i
  let x₂ : ℝ := ∑ i, a₂ i * y i
  let xk : ℝ := ∑ i, ak i * y i
  have hphase (t : ℝ) (a : ι → ℝ) :
      (∏ i, logPhase t (a i * y i)) = logPhase t (∑ i, a i * y i) :=
    (logPhase_sum Finset.univ t (fun i => a i * y i)).symm
  have hk' : P * paperRadialFourier W (R * Real.exp xk) =
      ∫ t : ℝ, P * logPhase t xk * b t := by
    simpa only [Finset.prod_mul_distrib, hphase, P, xk] using he y
  have hprod (t₁ t₂ t₃ : ℝ) :
      (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
        logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) =
      P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk := by
    simp only [Finset.prod_mul_distrib, hphase, P, x₁, x₂, xk]
  simp only [hprod, tripleCoefficient]
  have hinner (t₁ t₂ : ℝ) :
      (∫ t₃ : ℝ, (𝓕 g₁) t₁ * ((𝓕 g₂) t₂ * b t₃) *
        (P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk)) =
      ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [hk', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t₃
    ring
  simp_rw [hinner]
  have hmid (t₁ : ℝ) :
      (∫ t₂ : ℝ, ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk))) =
      (logPhase t₁ x₁ * (𝓕 g₁) t₁) * g₂ x₂ *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [schwartz_logPhase_inversion g₂ x₂, ← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t₂
    ring
  simp_rw [hmid]
  rw [integral_mul_const, integral_mul_const, ← schwartz_logPhase_inversion]
  dsimp only [P, x₁, x₂, xk]
  ring

theorem tripleCoefficient_weighted_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : Frequency =>
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) := by
  have hi (b : 𝓢(ℝ, ℂ)) : Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖b t‖) := by
    have he : (𝓕 (𝓕⁻ b) : 𝓢(ℝ, ℂ)) = b := by simp
    simpa only [he] using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J
  convert (hi b₁).mul_prod ((hi b₂).mul_prod (hi b₃)) using 1
  funext t
  simp only [tripleCoefficient, norm_mul]
  ring

theorem tripleCoefficient_weighted_integral (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ t : Frequency,
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) =
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₁ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₂ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) := by
  have he (t : Frequency) :
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖ =
      ((1 + ‖t.1‖)^J * ‖b₁ t.1‖) *
        (((1 + ‖t.2.1‖)^J * ‖b₂ t.2.1‖) * ((1 + ‖t.2.2‖)^J * ‖b₃ t.2.2‖)) := by
    simp only [tripleCoefficient, norm_mul]
    ring
  simp_rw [he]
  simp only [Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₁ t‖)
    (fun t : ℝ × ℝ => ((1 + ‖t.1‖)^J * ‖b₂ t.1‖) * ((1 + ‖t.2‖)^J * ‖b₃ t.2‖))]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₂ t‖) (fun t : ℝ => (1 + ‖t‖)^J * ‖b₃ t‖)]
  ring

end
end SevenEighths.InverseMoment

end OAI
