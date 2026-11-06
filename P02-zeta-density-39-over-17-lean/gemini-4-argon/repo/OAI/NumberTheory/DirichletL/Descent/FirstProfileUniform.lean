module
public import OAI.NumberTheory.DirichletL.Inversion.SecondProfileUniform

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson SevenEighths.InverseMoment SevenEighths.InverseInitialProfile SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseMomentFirstProfileUniform
export InverseSecondProfileUniform (rooted rooted_apply rooted_support translated translated_apply positiveSource)

abbrev normalization := InverseSecondProfileUniform.gen_normalization (9/2) InverseClippingProfiles.firstBalancedSlope
abbrev density := InverseSecondProfileUniform.gen_density (9/2) InverseClippingProfiles.firstBalancedSlope
abbrev profile := InverseSecondProfileUniform.gen_profile (9/2) InverseClippingProfiles.firstBalancedSlope firstLeftSlope firstRightSlope firstKernelSlope

theorem balanced_exponential_identity (ρ y : Fin 9 → ℝ) (c₁ c₂ L : ℝ) :
    normalization ρ c₁ c₂ L *
      (∏ i, Real.exp (InverseClippingProfiles.firstBalancedSlope i*(y i+ρ i))) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstLeftSlope i*y i)+Real.log c₁)) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstRightSlope i*y i)+Real.log c₂)) =
      Real.exp (-(9/2:ℝ)*L)*Real.exp (InverseClippingProfiles.firstRootExponent y) := by
  rw [normalization, InverseSecondProfileUniform.gen_normalization, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [InverseClippingProfiles.firstBalancedSlope,
    InverseClippingProfiles.firstRootExponent, firstLeftSlope, firstRightSlope,
    Fin.sum_univ_succ]
  ring

theorem balanced_profile_identity
    (U : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
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
        Φ (fun i y => U i (y+ρ i)) R y := by
  have he := congrArg (fun x : ℝ => (x : ℂ)) (balanced_exponential_identity ρ y c₁ c₂ L)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at he
  unfold profile InverseSecondProfileUniform.gen_profile firstPoissonProfile
  rw [InverseClippingProfiles.firstRootWindows_prod]
  simp only [translated_apply, clippedTwist_apply, rooted_apply, positiveSource, Real.log_exp,
    Finset.prod_mul_distrib]
  linear_combination
    (∏ i, U i (y i+ρ i)) * logPhase θ₁ (∑ i, firstLeftSlope i*y i) *
    g₁ ((∑ i, firstLeftSlope i*y i)+Real.log c₁) *
    logPhase θ₂ (∑ i, firstRightSlope i*y i) *
    g₂ ((∑ i, firstRightSlope i*y i)+Real.log c₂) *
    paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)) * he

theorem first_profile_common_measure
    (U : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
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
  dsimp only
  obtain ⟨C,hC,hs⟩ := InverseSecondProfileUniform.gen_common_measure (9/2) (by norm_num)
    InverseClippingProfiles.firstBalancedSlope firstLeftSlope firstRightSlope firstKernelSlope
    (fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i))
    (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂) Φ M B b hM hB
    (fun i => rooted_support _ _ _ _) A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,hb₃⟩ := hs R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ (zero_lt_one.trans_le hc₁)
    (zero_lt_one.trans_le hc₂) hc₁b hc₂b hL
  refine ⟨?_,h.2⟩
  intro y
  rw [← balanced_profile_identity U g₁ g₂ Φ M m₁ m₂ hU h₁ h₂]
  exact h.1 y
