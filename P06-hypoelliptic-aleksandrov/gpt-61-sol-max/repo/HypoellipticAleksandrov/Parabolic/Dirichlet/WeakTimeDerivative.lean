module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Gelfand weak time derivatives

This module defines the quotient-safe scalar testing relation for a reverse-time
Bochner `L²(V)` curve and its `L²(V*)` weak derivative.  It contains only the
basic linear algebra of that relation; endpoint, uniqueness, and smooth-curve
results belong to later modules.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance instReverseTimeL2VStarModule
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T)

private def weakDerivativeLeft

    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ :=
  fun tau => inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau

private def weakDerivativeRight

    (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun tau => (g tau) v * eta tau

private theorem weakDerivativeLeft_add_ae

    (u₁ u₂ : ReverseTimeL2V hΩ T) :
    weakDerivativeLeft hΩ T v eta (u₁ + u₂) =ᵐ[reverseTimeVolume T]
      weakDerivativeLeft hΩ T v eta u₁ + weakDerivativeLeft hΩ T v eta u₂ := by

  filter_upwards [Lp.coeFn_add (reverseTimeValueCLM hΩ T u₁)
    (reverseTimeValueCLM hΩ T u₂)] with tau ht
  dsimp only [weakDerivativeLeft]
  rw [((reverseTimeValueCLM hΩ T).map_add u₁ u₂), ht]
  change inner ℝ (valueCLM hΩ v)
    (reverseTimeValueCLM hΩ T u₁ tau + reverseTimeValueCLM hΩ T u₂ tau) * eta.deriv tau =
    inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u₁ tau) * eta.deriv tau +
      inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u₂ tau) * eta.deriv tau
  simp only [inner_add_right, add_mul]

private theorem weakDerivativeRight_add_ae

    (g₁ g₂ : ReverseTimeL2VStar hΩ T) :
    weakDerivativeRight hΩ T v eta (g₁ + g₂) =ᵐ[reverseTimeVolume T]
      weakDerivativeRight hΩ T v eta g₁ + weakDerivativeRight hΩ T v eta g₂ := by
  filter_upwards [Lp.coeFn_add g₁ g₂] with tau ht
  dsimp only [weakDerivativeRight]
  rw [ht]
  change ((g₁ tau + g₂ tau) v) * eta tau = (g₁ tau) v * eta tau + (g₂ tau) v * eta tau
  simp only [ContinuousLinearMap.add_apply, add_mul]

private theorem weakDerivativeLeft_smul_ae

    (u : ReverseTimeL2V hΩ T) (a : ℝ) :
    weakDerivativeLeft hΩ T v eta (a • u) =ᵐ[reverseTimeVolume T]
      a • weakDerivativeLeft hΩ T v eta u := by

  filter_upwards [Lp.coeFn_smul a (reverseTimeValueCLM hΩ T u)] with tau ht
  have ht' : ((a • reverseTimeValueCLM hΩ T u ) tau) =
      a • reverseTimeValueCLM hΩ T u tau := by
    exact ht
  dsimp only [weakDerivativeLeft]
  rw [((reverseTimeValueCLM hΩ T).map_smul a u), ht']
  simp only [weakDerivativeLeft, Pi.smul_apply, inner_smul_right, smul_eq_mul, mul_assoc]

private theorem weakDerivativeRight_smul_ae

    (g : ReverseTimeL2VStar hΩ T) (a : ℝ) :
    weakDerivativeRight hΩ T v eta (a • g ) =ᵐ[reverseTimeVolume T]
      a • weakDerivativeRight hΩ T v eta g := by
  filter_upwards [Lp.coeFn_smul  a g] with tau ht
  dsimp only [weakDerivativeRight]
  simpa only [weakDerivativeRight, Pi.smul_apply, smul_apply, smul_eq_mul, mul_assoc] using
    congrArg (fun q : H10HilbertGraphDual hΩ => q v * eta tau) ht

variable {α : Type _}

private theorem integral_neg_add
     [MeasurableSpace α] (μ : Measure α)
    {f₁ f₂ f g₁ g₂ g : α → ℝ}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ)
    (hg₁ : Integrable g₁ μ) (hg₂ : Integrable g₂ μ)
    (hleft : f =ᵐ[μ] f₁ + f₂) (hright : g =ᵐ[μ] g₁ + g₂)
    (hidentity₁ : (∫ x, f₁ x ∂μ) = -(∫ x, g₁ x ∂μ))
    (hidentity₂ : (∫ x, f₂ x ∂μ) = -(∫ x, g₂ x ∂μ)) :
    (∫ x, f x ∂μ) = -(∫ x, g x ∂μ) := by
  calc
    (∫ x, f x ∂μ) = ∫ x, f₁ x + f₂ x ∂μ := integral_congr_ae hleft
    _ = (∫ x, f₁ x ∂μ) + ∫ x, f₂ x ∂μ := integral_add hf₁ hf₂
    _ = -(∫ x, g₁ x ∂μ) + -(∫ x, g₂ x ∂μ) := by rw [hidentity₁, hidentity₂]
    _ = -((∫ x, g₁ x ∂μ) + ∫ x, g₂ x ∂μ) := by ring
    _ = -(∫ x, g₁ x + g₂ x ∂μ) := by rw [integral_add hg₁ hg₂]
    _ = -(∫ x, g x ∂μ) := congrArg Neg.neg (integral_congr_ae hright).symm

private theorem integral_neg_smul
     [MeasurableSpace α] (μ : Measure α)
    {f fScaled g gScaled : α → ℝ} (a : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hleft : fScaled =ᵐ[μ] a • f) (hright : gScaled =ᵐ[μ] a • g)
    (hidentity : (∫ x, f x ∂μ) = -(∫ x, g x ∂μ)) :
    (∫ x, fScaled x ∂μ) = -(∫ x, gScaled x ∂μ) := by
  calc
    (∫ x, fScaled x ∂μ) = ∫ x, a • f x ∂μ := integral_congr_ae hleft
    _ = a • ∫ x, f x ∂μ := hf.integral_smul a
    _ = -(a • ∫ x, g x ∂μ) := by rw [hidentity, smul_neg]
    _ = -(∫ x, a • g x ∂μ) := by rw [hg.integral_smul a]
    _ = -(∫ x, gScaled x ∂μ) := congrArg Neg.neg (integral_congr_ae hright).symm

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

variable (hΩ : IsOpen Ω) (T : ℝ)

/-- The Gelfand weak reverse-time derivative identity against compactly
supported scalar tests.  The derivative is the ordinary positive-time
derivative of the test, so the distributional sign appears on the right. -/
def HasGelfandWeakTimeDerivative

     (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : Prop :=
  ∀ v : H10HilbertGraph hΩ, ∀ eta : ReverseTimeScalarTest T,
    Integrable
      (fun tau =>
        inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau)
      (reverseTimeVolume T) ∧
    Integrable
      (fun tau => (g tau) v * eta tau)
      (reverseTimeVolume T) ∧
    (∫ tau,
      inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau
      ∂reverseTimeVolume T) =
      -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T)

/-- The left-hand scalar pairing in the Gelfand weak derivative identity is
integrable by the Bochner `L²` carrier and Hölder's inequality. -/
theorem integrable_reverseTimeWeakDerivative_left


    (u : ReverseTimeL2V hΩ T)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    Integrable
      (fun tau =>
        inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau)
      (reverseTimeVolume T) := (MemLp.integrable_mul
  (MemLp.continuousLinearMap_comp (Lp.memLp ((reverseTimeValueCLM hΩ T) u)) ((innerSL ℝ) ((valueCLM hΩ) v)))
  (ReverseTimeScalarTest.memLp_deriv eta 2))

/-- The right-hand dual pairing in the Gelfand weak derivative identity is
integrable by the Bochner `L²` carrier and Hölder's inequality. -/
theorem integrable_reverseTimeWeakDerivative_right


    (g : ReverseTimeL2VStar hΩ T)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    Integrable
      (fun tau => (g tau) v * eta tau)
      (reverseTimeVolume T) := (MemLp.integrable_mul (MemLp.continuousLinearMap_comp (Lp.memLp g) ((ContinuousLinearMap.apply ℝ ℝ) v))
  (ReverseTimeScalarTest.memLp eta 2))

variable {hΩ : IsOpen Ω} {T : ℝ} {hT : 0 < T}

/-- Gelfand weak time derivatives are closed under addition. -/
theorem HasGelfandWeakTimeDerivative.add


    {u₁ u₂ : ReverseTimeL2V hΩ T} {g₁ g₂ : ReverseTimeL2VStar hΩ T}
    (h₁ : HasGelfandWeakTimeDerivative hΩ T hT u₁ g₁)
    (h₂ : HasGelfandWeakTimeDerivative hΩ T hT u₂ g₂) :
    HasGelfandWeakTimeDerivative hΩ T hT (u₁ + u₂) (g₁ + g₂) := (fun v eta =>
  And.casesOn (h₁ v eta) fun hleft₁ right =>
    And.casesOn right fun hright₁ hidentity₁ =>
      And.casesOn (h₂ v eta) fun hleft₂ right =>
        And.casesOn right fun hright₂ hidentity₂ =>
          id
            (fun hleft₁ =>
              id
                (fun hright₁ =>
                  id
                    (fun hidentity₁ =>
                      id
                        (fun hleft₂ =>
                          id
                            (fun hright₂ =>
                              id
                                (fun hidentity₂ =>
                                  id
                                    ⟨integrable_reverseTimeWeakDerivative_left hΩ T (u₁ + u₂) v eta,
                                      ⟨integrable_reverseTimeWeakDerivative_right hΩ T (g₁ + g₂) v eta,
                                        integral_neg_add (reverseTimeVolume T) hleft₁ hleft₂ hright₁ hright₂
                                          (weakDerivativeLeft_add_ae hΩ T v eta u₁ u₂)
                                          (weakDerivativeRight_add_ae hΩ T v eta g₁ g₂) hidentity₁ hidentity₂⟩⟩)
                                hidentity₂)
                            hright₂)
                        hleft₂)
                    hidentity₁)
                hright₁)
            hleft₁)

/-- Gelfand weak time derivatives are closed under scalar multiplication. -/
theorem HasGelfandWeakTimeDerivative.smul


    {u : ReverseTimeL2V hΩ T} {g : ReverseTimeL2VStar hΩ T}
    (h : HasGelfandWeakTimeDerivative hΩ T hT u g) (a : ℝ) :
    HasGelfandWeakTimeDerivative hΩ T hT (a • u) (a • g ) := by
  intro v eta
  obtain ⟨hleft, hright, hidentity⟩ := h v eta
  refine ⟨integrable_reverseTimeWeakDerivative_left hΩ T (a • u) v eta,
    integrable_reverseTimeWeakDerivative_right hΩ T _ v eta, ?_⟩
  exact integral_neg_smul _ a hleft hright
    (weakDerivativeLeft_smul_ae hΩ T v eta u a)
    (weakDerivativeRight_smul_ae hΩ T v eta g a) hidentity

/-- The weak derivative relation respects equality of its two bundled curves. -/
theorem HasGelfandWeakTimeDerivative.congr


    {u u' : ReverseTimeL2V hΩ T} {g g' : ReverseTimeL2VStar hΩ T}
    (h : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (hu : u = u') (hg : g = g') :
    HasGelfandWeakTimeDerivative hΩ T hT u' g' := by
  subst u'
  subst g'
  exact h

end HypoellipticAleksandrov.Parabolic.Dirichlet
