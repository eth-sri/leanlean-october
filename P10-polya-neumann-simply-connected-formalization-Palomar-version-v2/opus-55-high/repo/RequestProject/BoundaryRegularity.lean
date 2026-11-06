module

public import RequestProject.BoundaryChart
public import RequestProject.ArcLength
public import RequestProject.SmoothDomain
public import RequestProject.ReconChordArc

/-!
# Regularity of the constant-speed boundary parametrization of a smooth domain

For a smooth domain `Ω`, a boundary parametrization `γ` in the sense of `IsBoundaryParam`
(Lipschitz, `2π`-periodic, injective on `[0, 2π)`, onto `∂Ω`, with constant speed a.e.) is
`C^{1,1}`: `γ` is differentiable everywhere and `γ'` is Lipschitz on `[0, 2π]`
(`IsBoundaryParam.deriv_lipschitz`). This is the regularity hypothesis on the curve used in the
fractional regularity of the corrected kernel (Lemma 6.6).

In a smooth chart `w = p + c̄ (x + i f(x))` the abscissa `X(θ) = Re(c(γ(θ) - p))` is Lipschitz and
strictly monotone (`γ` is injective), so the constant speed gives
`γ'(θ) = Φ(X(θ))` almost everywhere, with the smooth field
`Φ(x) = c̄ (1 + i f'(x)) σ c₀ / √(1 + f'(x)²)` (`σ = ±1` the orientation). Since `γ` is the integral
of its derivative, `γ' = Φ ∘ X` everywhere, which is Lipschitz.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann


variable {Ω : Set ℂ} {γ : ℝ → ℂ}









end PolyaNeumann
