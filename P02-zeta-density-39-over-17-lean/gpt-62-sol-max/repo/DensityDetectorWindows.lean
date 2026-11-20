module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
meta import Mathlib.Tactic

@[expose] public section

namespace Montgomery.RationalMoment
noncomputable section

/-- Pure parameter conditions for the actual two-term-energy route. None
of these fields is an assumed analytic estimate or a counting conclusion. -/
structure TwoTermWindow (σ a p α : ℝ) : Prop where
  sigma_low : 9/13 ≤ σ
  sigma_high : σ ≤ 3/4
  a_low : 7/10 ≤ a
  a_high : a ≤ 4/5
  p_low : 3/5 ≤ p
  alpha_low : a ≤ α
  alpha_high : α ≤ 1
  p_identity : p=3*a*(1-σ)
  mean_identity : 1+α*(1-2*σ)=p
  energy_range : 2*(1-a) ≤ p
  amplifier_lower : 0 ≤ p+α*(6*σ-5)
  cubic_lower : 4/5 ≤ p+a*(6*σ-4)
  amplifier_upper : p+α*(6*σ-4) ≤ 1
  cubic_balance : 2 ≤ 5*p/2+a*(12*σ-8)
  energy_first : 1+α*(6-8*σ) ≤ 2*p
  energy_resonant : 1+a*(9/2-7*σ) ≤ p
  typeII : 2-2*σ+1/25 ≤ p

/-- All endpoints and length-window budgets for the first two-term branch. -/
theorem two_term_window_first (s : ℝ) (hl : (12/17:ℝ) ≤ s) (hr : s ≤ (5/7:ℝ)) :
    TwoTermWindow s (2/(8*s-3)) (6*(1-s)/(8*s-3)) ((14*s-9)/((8*s-3)*(2*s-1))) := by
  have hD₀ : 0 < 8*s-3 := by linarith
  have hD : 0 < s*8-3 := by linarith
  have hE₀ : 0 < 2*s-1 := by linarith
  have hE : 0 < s*2-1 := by linarith
  have h₀ := sq_nonneg (s-(12/17:ℝ))
  have h₁ := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)
  have h₂ := sq_nonneg ((5/7:ℝ)-s)
  constructor <;> (try field_simp [hD,hE,hD₀,hE₀]) <;> nlinarith only [hl, hr, h₀, h₁, h₂]

structure AdjacentWindow (σ a p α : ℝ) : Prop where
  sigma_low : 9/13 ≤ σ
  sigma_high : σ ≤ 3/4
  a_low : 7/10 ≤ a
  a_high : a ≤ 4/5
  p_low : 5/9 ≤ p
  alpha_low : a ≤ α
  alpha_high : α ≤ 1
  p_identity : p=3*a*(1-σ)
  mean_identity : 1+α*(1-2*σ)=p
  amplifier_lower : 0 ≤ p+α*(6*σ-5)
  cubic_lower : 4/5 ≤ p+a*(6*σ-4)
  amplifier_upper : p+α*(6*σ-4) ≤ 1
  cubic_balance : 2 ≤ 5*p/2+a*(12*σ-8)
  energy_first : 1+α*(6-8*σ) ≤ 2*p
  energy_resonant : 1+a*(9/2-7*σ) ≤ p
  energy_adjacent_third : 3 ≤ (5/2)*p+a*(14*σ-8)
  energy_adjacent_fourth : 9/4 ≤ (29/12)*p+a*(14*σ-9)
  typeII : 2-2*σ+1/50 ≤ p

/-- All endpoints and length-window budgets for the second two-term branch. -/
theorem adjacent_window_second (s : ℝ) (hl : (5/7:ℝ) ≤ s) (hr : s ≤ (113/153:ℝ)) :
    AdjacentWindow s (4/(9*s-1)) (12*(1-s)/(9*s-1)) ((21*s-13)/((9*s-1)*(2*s-1))) := by
  have hD₀ : 0 < 9*s-1 := by linarith
  have hD : 0 < s*9-1 := by linarith
  have hE₀ : 0 < 2*s-1 := by linarith
  have hE : 0 < s*2-1 := by linarith
  have h₀ := sq_nonneg (s-(5/7:ℝ))
  have h₁ := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)
  have h₂ := sq_nonneg ((113/153:ℝ)-s)
  constructor <;> (try field_simp [hD,hE,hD₀,hE₀]) <;> nlinarith only [hl, hr, h₀, h₁, h₂]

/-- Explicit amplifier exponent for the third orange branch. -/
def thirdAmplifierExponent (σ p x : ℝ) : ℝ :=
  max x (max (5/6:ℝ) (2+(4-6*σ)*x-3*p/2))

/-- Only arithmetic inequalities appear in this window. Its analytic
consequences are proved separately and its pictured parameters are discharged. -/
structure ThirdWindow (σ a p α : ℝ) : Prop where
  sigma_low : 9/13 ≤ σ
  sigma_high : σ ≤ 3/4
  a_low : 69/100 ≤ a
  a_high : a ≤ 4/5
  p_low : 1/2 ≤ p
  alpha_low : a ≤ α
  alpha_high : α ≤ 1
  p_identity : p=3*a*(1-σ)
  mean_identity : 1+α*(1-2*σ)=p
  typeII : 2-2*σ+1/50 ≤ p
  budgets : ∀ x : ℝ, a ≤ x → x ≤ α →
    let l := thirdAmplifierExponent σ p x
    l ≤ 1 ∧ l ≤ p+(2*σ-1)*x ∧ l ≤ p+(6*σ-4)*x ∧
    l ≤ (49/40)*p+(6*σ-4)*x-1/8 ∧
    2 ≤ 4*p+(16*σ-12)*x ∧
    2 ≤ 2*p+(14*σ-9)*x ∧
    3 ≤ (5/2)*p+(14*σ-8)*x ∧
    9/4 ≤ (29/12)*p+(14*σ-9)*x ∧
    1 ≤ (5/4)*p+(6*σ-4)*x

lemma affine_nonneg_between {a b x q r : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (h₁ : 0 ≤ q*a+r) (h₂ : 0 ≤ q*b+r) : 0 ≤ q*x+r := by
  by_cases hq : 0 ≤ q
  · have := mul_le_mul_of_nonneg_left ha hq
    linarith
  · have := mul_le_mul_of_nonpos_left hb (le_of_not_ge hq)
    linarith

/-- Every exponent and detecting length for the full third orange segment. -/
theorem third_window_parameters (s : ℝ) (hl : (113/153:ℝ) ≤ s) (hr : s ≤ (3/4:ℝ)) :
    ThirdWindow s (85/(153*s+7)) (255*(1-s)/(153*s+7)) ((408*s-248)/((153*s+7)*(2*s-1))) := by
  have hD₀ : 0 < 153*s+7 := by linarith
  have hD : 0 < s*153+7 := by linarith
  have hE₀ : 0 < 2*s-1 := by linarith
  have hE : 0 < s*2-1 := by linarith
  have h₀ := sq_nonneg (s-(113/153:ℝ))
  have h₁ := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)
  have h₂ := sq_nonneg ((3/4:ℝ)-s)
  let a : ℝ := 85/(153*s+7)
  let p : ℝ := 255*(1-s)/(153*s+7)
  let u : ℝ := (408*s-248)/((153*s+7)*(2*s-1))
  change ThirdWindow s a p u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  any_goals ((try dsimp only [a, p, u]); (try field_simp [hD,hE,hD₀,hE₀]); nlinarith only [hl, hr, h₀, h₁, h₂])
  intro x hx hu
  dsimp only
  simp only [thirdAmplifierExponent, max_le_iff]
  repeat' apply And.intro
  all_goals apply le_of_sub_nonneg
  all_goals
    first
    | suffices 0 ≤ (-1)*x+(1) by linarith only [this]
    | suffices 0 ≤ (0)*x+(1/6) by linarith only [this]
    | suffices 0 ≤ (6*s-4)*x+(3*p/2-1) by linarith only [this]
    | suffices 0 ≤ (2*s-2)*x+(p) by linarith only [this]
    | suffices 0 ≤ (2*s-1)*x+(p-5/6) by linarith only [this]
    | suffices 0 ≤ (8*s-5)*x+(5*p/2-2) by linarith only [this]
    | suffices 0 ≤ (6*s-5)*x+(p) by linarith only [this]
    | suffices 0 ≤ (6*s-4)*x+(p-5/6) by linarith only [this]
    | suffices 0 ≤ (12*s-8)*x+(5*p/2-2) by linarith only [this]
    | suffices 0 ≤ (6*s-5)*x+(49*p/40-1/8) by linarith only [this]
    | suffices 0 ≤ (6*s-4)*x+(49*p/40-23/24) by linarith only [this]
    | suffices 0 ≤ (12*s-8)*x+(109*p/40-17/8) by linarith only [this]
    | suffices 0 ≤ (16*s-12)*x+(4*p-2) by linarith only [this]
    | suffices 0 ≤ (14*s-9)*x+(2*p-2) by linarith only [this]
    | suffices 0 ≤ (14*s-8)*x+(5*p/2-3) by linarith only [this]
    | suffices 0 ≤ (14*s-9)*x+(29*p/12-9/4) by linarith only [this]
    apply affine_nonneg_between hx hu <;> dsimp only [a, p, u] <;>
      (try field_simp [hD,hE,hD₀,hE₀]) <;> nlinarith only [hl, hr, h₀, h₁, h₂]

end
end Montgomery.RationalMoment
