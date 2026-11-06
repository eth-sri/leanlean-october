module
public import OAI.NumberTheory.DirichletL.Inversion.SecondProfileUniform
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseMomentFirstProfileUniform

export OAI.SevenEighths.InverseSecondProfileUniform (translated_box fourier_translated rooted_apply rooted_support rooted translated_apply positiveSource translated)

def normalization (ρ : Fin 9 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-(9/2:ℝ)*L - ∑ i, InverseClippingProfiles.firstBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem density_formula (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) :
    density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p =
      (normalization ρ c₁ c₂ L : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 * (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) *
        (∏ i, logPhase (p.2 i) (ρ i) * (𝓕 (g i)) (p.2 i)) := by
  pm_204 density fullProfileDensity tripleCoefficient coordinateDensity fourier_translated fourier_clippedTwist
  ring

private theorem fourier_twist (g : 𝓢(ℝ, ℂ)) (θ t : ℝ) :
    (𝓕 (frequencyTwist g θ)) t = (𝓕 g) (t-θ) := by pm_3202

theorem density_norm (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) :
    ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖ = normalization ρ c₁ c₂ L *
      ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖ := by pm_3203

theorem normalization_bound (B : Fin 9 → ℝ) (b : ℝ)
    (ρ : Fin 9 → ℝ) (c₁ c₂ L : ℝ) (hρ : ∀ i, |ρ i| ≤ B i)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) (hL : 0 ≤ L) :
    normalization ρ c₁ c₂ L ≤
      Real.exp ((∑ i, |InverseClippingProfiles.firstBalancedSlope i| *B i)+Real.log b) := by
  pm_3204 InverseClippingProfiles.firstBalancedSlope

theorem density_weighted_integrable (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) := by pf_229

private theorem radial_common_box (Φ : 𝓢(ℝ, ℂ)) (M : Fin 9 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (V : Fin 9 → ℝ → ℂ), (∀ i y, V i y ≠ 0 → |y| ≤ M i) →
        ∀ y : Fin 9 → ℝ,
        (∏ i, V i (y i))*paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)) =
          ∫ t : ℝ, (∏ i, V i (y i)*logPhase t (firstKernelSlope i*y i))*b₃ t) ∧
      (1+R)^A * (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) ≤ C := by pf_89 9 firstKernelSlope

theorem density_weighted_integral (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Ambient (Fin 9), ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) = normalization ρ c₁ c₂ L *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₁ θ₁)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₂ θ₂)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
        (∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖) := by pf_149 9

def profile (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, firstLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, firstRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)))

theorem common_measure (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 9 → ℝ) (b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hg : ∀ i, Function.support (g i) ⊆ Set.Icc (-M i) (M i)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 0 < c₁ → 0 < c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 9 → ℝ, profile g g₁ g₂ Φ ρ c₁ c₂ θ₁ θ₂ R L y =
        ∫ p : Ambient (Fin 9), density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 9), ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by pf_39 InverseClippingProfiles.firstBalancedSlope firstLeftSlope firstRightSlope firstKernelSlope

theorem balanced_exponential_identity (ρ y : Fin 9 → ℝ) (c₁ c₂ L : ℝ) :
    normalization ρ c₁ c₂ L *
      (∏ i, Real.exp (InverseClippingProfiles.firstBalancedSlope i*(y i+ρ i))) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstLeftSlope i*y i)+Real.log c₁)) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstRightSlope i*y i)+Real.log c₂)) =
      Real.exp (-(9/2:ℝ)*L)*Real.exp (InverseClippingProfiles.firstRootExponent y) := by
  pm_5669
  norm_num [InverseClippingProfiles.firstBalancedSlope,
    InverseClippingProfiles.firstRootExponent, firstLeftSlope, firstRightSlope,
    Fin.sum_univ_succ]
  ring

section
variable (U : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
include U g₁ g₂ Φ
theorem balanced_profile_identity
    (M : Fin 9 → ℝ) (m₁ m₂ : ℝ)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂)
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 9 → ℝ) :
    profile (fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i))
      (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
      Φ ρ c₁ c₂ θ₁ θ₂ R L y =
      (Real.exp (-(9/2:ℝ)*L) : ℂ) * firstPoissonProfile
        (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
        Φ (fun i y => U i (y+ρ i)) R y := by pm_3205 firstPoissonProfile InverseClippingProfiles.firstRootWindows_prod firstLeftSlope firstRightSlope firstKernelSlope

theorem first_profile_common_measure
    (M B : Fin 9 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 9 → ℝ,
        (Real.exp (-(9/2:ℝ)*L) : ℂ) * firstPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 9), density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 9), ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  pm_3207 InverseClippingProfiles.firstBalancedSlope
  pm_3206
end

end SevenEighths.InverseMomentFirstProfileUniform

end

end OAI
